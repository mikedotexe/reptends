#!/usr/bin/env python3
"""Resumable AWS hosting for the single-file reptends site. Requires AWS CLI v2."""
import argparse
import csv
from contextlib import contextmanager
import fcntl
import hashlib
import http.client
import ipaddress
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import uuid
from datetime import datetime, timezone

DIRECTORY = Path(__file__).resolve().parent
STATE_FILE = DIRECTORY / "hosting.json"
ACCOUNT = "341982967115"
REGION = "us-east-1"
PROFILE = "reptends"
DOMAIN = "reptends.mikedotexe.com"
BUCKET = "reptends-mikedotexe-com-341982967115"
ZONE = "ZEBBWSGTKUUP6"
CLOUDFRONT_ZONE = "Z2FDTNDATAQYW2"


def now():
    return datetime.now(timezone.utc).isoformat()


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def load_state():
    if STATE_FILE.exists():
        state = json.loads(STATE_FILE.read_text())
        for key, expected in [("account", ACCOUNT), ("region", REGION),
                              ("bucket", BUCKET), ("domain", DOMAIN), ("zone", ZONE)]:
            if state.get(key) != expected:
                raise RuntimeError(f"Unexpected {key} in hosting.json; refusing to provision.")
        return state
    state = dict(account=ACCOUNT, region=REGION, profile=PROFILE, bucket=BUCKET,
                 domain=DOMAIN, zone=ZONE, created_at=now(),
                 certificate_token=uuid.uuid4().hex,
                 distribution_caller_reference="reptends-" + uuid.uuid4().hex,
                 oac_name="reptends-mikedotexe-com")
    save(state)
    return state


def save(state):
    state["updated_at"] = now()
    atomic_json(STATE_FILE, state)


def aws(service, operation, *arguments, environment=None, profile=PROFILE):
    command = ["aws", "--region", REGION, "--output", "json", "--no-cli-pager"]
    if environment is None:
        command += ["--profile", profile]
    command += [service, operation, *map(str, arguments)]
    result = subprocess.run(command, capture_output=True, text=True, env=environment)
    if result.returncode:
        error = result.stderr.strip()
        if environment is not None:
            for name in ["AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_SESSION_TOKEN"]:
                value = environment.get(name)
                if value:
                    error = error.replace(value, "[redacted]")
        raise RuntimeError(f"{service} {operation}: {error}")
    return json.loads(result.stdout) if result.stdout.strip() else {}


def identity(environment=None):
    result = aws("sts", "get-caller-identity", environment=environment)
    expected = f"arn:aws:iam::{ACCOUNT}:user/reptends-deployer"
    if result.get("Account") != ACCOUNT or result.get("Arn") != expected:
        raise RuntimeError("Credentials do not identify the approved reptends-deployer user.")
    return expected


def replace_ini_section(path, name, values):
    """Change this profile only, preserving all other sections byte-for-byte."""
    original = path.read_text() if path.exists() else ""
    pattern = re.compile(r"(?m)^\[" + re.escape(name) + r"\][^\n]*(?:\n(?!\[)[^\n]*)*")
    section = "[" + name + "]\n" + "".join(f"{key} = {value}\n" for key, value in values.items())
    updated = pattern.sub(section.rstrip("\n"), original) if pattern.search(original) else original.rstrip("\n") + ("\n\n" if original else "") + section
    temporary = path.with_name(path.name + ".reptends.tmp")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(descriptor, "w") as handle:
        handle.write(updated.rstrip("\n") + "\n")
    os.chmod(temporary, 0o600)
    temporary.replace(path)


def configure_profile(csv_path):
    with csv_path.open(newline="", encoding="utf-8-sig") as handle:
        rows = list(csv.DictReader(handle))
    if len(rows) != 1:
        raise RuntimeError("Expected exactly one credential row.")
    fields = {key.lower().strip(): value.strip() for key, value in rows[0].items()}
    access = fields.get("access key id", "")
    secret = fields.get("secret access key", "")
    if not access or not secret or any("\n" in item or "\r" in item for item in [access, secret]):
        raise RuntimeError("CSV does not contain valid credential fields.")
    environment = os.environ.copy()
    for key in ["AWS_PROFILE", "AWS_DEFAULT_PROFILE", "AWS_SESSION_TOKEN"]:
        environment.pop(key, None)
    environment.update(AWS_ACCESS_KEY_ID=access, AWS_SECRET_ACCESS_KEY=secret,
                       AWS_DEFAULT_REGION=REGION)
    arn = identity(environment)
    folder = Path.home() / ".aws"
    folder.mkdir(mode=0o700, exist_ok=True)
    replace_ini_section(folder / "credentials", PROFILE,
                        {"aws_access_key_id": access, "aws_secret_access_key": secret})
    replace_ini_section(folder / "config", "profile " + PROFILE,
                        {"region": REGION, "output": "json"})
    print(f"Configured profile {PROFILE} for {arn}; no credentials were printed.")


def json_argument(value):
    return json.dumps(value, separators=(",", ":"))


def change_records(state, changes, state_key):
    response = aws("route53", "change-resource-record-sets", "--hosted-zone-id", ZONE,
                   "--change-batch", json_argument({"Changes": changes}))
    state[state_key] = response["ChangeInfo"]["Id"]
    save(state)


def records():
    return aws("route53", "list-resource-record-sets", "--hosted-zone-id", ZONE)["ResourceRecordSets"]


def provision(state):
    identity()
    if not state.get("preflight_done"):
        zone = aws("route53", "get-hosted-zone", "--id", ZONE)["HostedZone"]
        if zone["Name"] != "mikedotexe.com." or zone["Config"]["PrivateZone"]:
            raise RuntimeError("The approved hosted zone is not the expected public zone.")
        if any(record["Name"].rstrip(".") == DOMAIN for record in records()):
            raise RuntimeError("The site DNS name already exists; inspect it before provisioning.")
        state["preflight_done"] = True
        save(state)
    if not state.get("bucket_created"):
        aws("s3api", "create-bucket", "--bucket", BUCKET)
        state["bucket_created"] = True
        save(state)
        print("Created dedicated S3 bucket.", flush=True)
    if not state.get("bucket_configured"):
        aws("s3api", "put-public-access-block", "--bucket", BUCKET,
            "--public-access-block-configuration", json_argument({key: True for key in
              ["BlockPublicAcls", "IgnorePublicAcls", "BlockPublicPolicy", "RestrictPublicBuckets"]}))
        aws("s3api", "put-bucket-ownership-controls", "--bucket", BUCKET,
            "--ownership-controls", json_argument({"Rules": [{"ObjectOwnership": "BucketOwnerEnforced"}]}))
        aws("s3api", "put-bucket-encryption", "--bucket", BUCKET,
            "--server-side-encryption-configuration", json_argument({"Rules": [{
                "ApplyServerSideEncryptionByDefault": {"SSEAlgorithm": "AES256"}}]}))
        state["bucket_configured"] = True
        save(state)
    if not state.get("certificate_arn"):
        response = aws("acm", "request-certificate", "--domain-name", DOMAIN,
                       "--validation-method", "DNS", "--key-algorithm", "RSA_2048",
                       "--idempotency-token", state["certificate_token"])
        state["certificate_arn"] = response["CertificateArn"]
        save(state)
        print("Requested exact-domain ACM certificate.", flush=True)
    certificate = aws("acm", "describe-certificate", "--certificate-arn", state["certificate_arn"])["Certificate"]
    state["certificate_status"] = certificate["Status"]
    save(state)
    validation = next((item["ResourceRecord"] for item in certificate.get("DomainValidationOptions", []) if "ResourceRecord" in item), None)
    if validation and not state.get("certificate_dns_change_id"):
        state["certificate_validation_record"] = validation
        save(state)
        change_records(state, [{"Action": "UPSERT", "ResourceRecordSet": {
            "Name": validation["Name"], "Type": validation["Type"], "TTL": 300,
            "ResourceRecords": [{"Value": validation["Value"]}]}}], "certificate_dns_change_id")
        print("Created ACM validation CNAME; site A/AAAA records remain gated.", flush=True)
    if certificate["Status"] != "ISSUED":
        if certificate["Status"] not in ["PENDING_VALIDATION"]:
            raise RuntimeError("Certificate status: " + certificate["Status"])
        print("Certificate validation pending. Run provision again to continue.")
        return
    if not state.get("oac_id"):
        if state.get("oac_create_pending"):
            raise RuntimeError("Previous OAC creation outcome is unknown. Recover its ID by name using an administrator before retrying.")
        state["oac_create_pending"] = True
        save(state)
        response = aws("cloudfront", "create-origin-access-control", "--origin-access-control-config",
                       json_argument({"Name": state["oac_name"], "Description": "Private origin for reptends.mikedotexe.com",
                                      "SigningProtocol": "sigv4", "SigningBehavior": "always", "OriginAccessControlOriginType": "s3"}))
        state["oac_id"] = response["OriginAccessControl"]["Id"]
        state.pop("oac_create_pending", None)
        save(state)
    if not state.get("distribution_id"):
        config = {
            "CallerReference": state["distribution_caller_reference"],
            "Aliases": {"Quantity": 1, "Items": [DOMAIN]},
            "DefaultRootObject": "index.html",
            "Origins": {"Quantity": 1, "Items": [{"Id": "reptends-s3", "DomainName": f"{BUCKET}.s3.{REGION}.amazonaws.com",
                "S3OriginConfig": {"OriginAccessIdentity": ""}, "OriginAccessControlId": state["oac_id"]}]},
            "DefaultCacheBehavior": {"TargetOriginId": "reptends-s3", "ViewerProtocolPolicy": "redirect-to-https",
                "AllowedMethods": {"Quantity": 2, "Items": ["GET", "HEAD"], "CachedMethods": {"Quantity": 2, "Items": ["GET", "HEAD"]}},
                "Compress": True, "CachePolicyId": "658327ea-f89d-4fab-a63d-7e88639e58f6"},
            "Comment": "Reptends: an interactive, single-file mathematics essay",
            "PriceClass": "PriceClass_100", "Enabled": True, "IsIPV6Enabled": True,
            "HttpVersion": "http2and3", "ViewerCertificate": {"ACMCertificateArn": state["certificate_arn"],
                "SSLSupportMethod": "sni-only", "MinimumProtocolVersion": "TLSv1.2_2021"}
        }
        atomic_json(DIRECTORY / "distribution-config.json", config)
        response = aws("cloudfront", "create-distribution", "--distribution-config", json_argument(config))["Distribution"]
        state.update(distribution_id=response["Id"], distribution_arn=response["ARN"], distribution_domain=response["DomainName"], distribution_status=response["Status"])
        save(state)
        print("Created CloudFront distribution " + state["distribution_id"], flush=True)
    if not state.get("bucket_policy_configured"):
        policy = {"Version": "2012-10-17", "Statement": [{"Sid": "AllowReptendsCloudFrontReadIndex",
            "Effect": "Allow", "Principal": {"Service": "cloudfront.amazonaws.com"}, "Action": "s3:GetObject",
            "Resource": f"arn:aws:s3:::{BUCKET}/index.html", "Condition": {"StringEquals": {"AWS:SourceArn": state["distribution_arn"]}}}]}
        aws("s3api", "put-bucket-policy", "--bucket", BUCKET, "--policy", json_argument(policy))
        state["bucket_policy_configured"] = True
        save(state)
        atomic_json(DIRECTORY / "bucket-policy.json", policy)
    publisher = {"Version": "2012-10-17", "Statement": [
        {"Sid": "PublishIndex", "Effect": "Allow", "Action": "s3:PutObject", "Resource": f"arn:aws:s3:::{BUCKET}/index.html"},
        {"Sid": "RefreshAndObserveSiteCache", "Effect": "Allow", "Action": ["cloudfront:CreateInvalidation", "cloudfront:GetInvalidation"], "Resource": state["distribution_arn"]}]}
    atomic_json(DIRECTORY / "publisher-policy.json", publisher)
    status(state)


def status(state):
    result = {"bucket": BUCKET, "site_dns_published": state.get("site_dns_published", False)}
    if state.get("certificate_arn"):
        certificate = aws("acm", "describe-certificate", "--certificate-arn", state["certificate_arn"])["Certificate"]
        state["certificate_status"] = result["certificate_status"] = certificate["Status"]
    if state.get("distribution_id"):
        distribution = aws("cloudfront", "get-distribution", "--id", state["distribution_id"])["Distribution"]
        state["distribution_status"] = result["distribution_status"] = distribution["Status"]
        result["distribution_id"] = state["distribution_id"]
        result["distribution_domain"] = state["distribution_domain"]
    for field in ["certificate_dns_change_id", "site_dns_change_id"]:
        if state.get(field):
            result[field.replace("_id", "_status")] = aws("route53", "get-change", "--id", state[field])["ChangeInfo"]["Status"]
    state["ready_for_qa_gated_publish"] = bool(state.get("bucket_policy_configured") and state.get("certificate_status") == "ISSUED" and state.get("distribution_status") == "Deployed")
    result["ready_for_qa_gated_publish"] = state["ready_for_qa_gated_publish"]
    save(state)
    print(json.dumps(result, indent=2))


def publish(state, html_path, qa_passed):
    if not qa_passed:
        raise RuntimeError("Publishing requires --qa-passed after the exact HTML passes review.")
    identity()
    if not state.get("ready_for_qa_gated_publish"):
        raise RuntimeError("Run provision/status until infrastructure is ready.")
    data = html_path.read_bytes()
    if not data or len(data) > 5 * 1024 * 1024 * 1024:
        raise RuntimeError("Expected a nonempty, single-upload HTML file.")
    digest = hashlib.sha256(data).hexdigest()
    aws("s3api", "put-object", "--bucket", BUCKET, "--key", "index.html", "--body", html_path.resolve(),
        "--content-type", "text/html; charset=utf-8", "--cache-control", "max-age=60")
    state["published_sha256"] = digest
    state["published_at"] = now()
    save(state)
    invalidation = aws("cloudfront", "create-invalidation", "--distribution-id", state["distribution_id"], "--paths", "/*")["Invalidation"]
    state["invalidation_id"] = invalidation["Id"]
    state["invalidation_status"] = invalidation["Status"]
    save(state)
    print("Uploaded reviewed index.html and requested cache invalidation.")


def activate_dns(state, qa_passed):
    if not qa_passed or not state.get("published_sha256"):
        raise RuntimeError("DNS activation requires --qa-passed and a published HTML file.")
    if state.get("cloudfront_verified_sha256") != state["published_sha256"]:
        raise RuntimeError("Verify the published file at CloudFront before activating DNS.")
    identity()
    if state.get("site_dns_published"):
        print("Site DNS was already activated; retained existing records.")
        return
    aliases = [{"Action": "CREATE", "ResourceRecordSet": {"Name": DOMAIN, "Type": kind,
                "AliasTarget": {"HostedZoneId": CLOUDFRONT_ZONE, "DNSName": state["distribution_domain"], "EvaluateTargetHealth": False}}}
               for kind in ["A", "AAAA"]]
    existing = [record for record in records() if record["Name"].rstrip(".") == DOMAIN]
    if existing:
        expected = {item["ResourceRecordSet"]["Type"] for item in aliases}
        if {item["Type"] for item in existing} != expected or any(item.get("AliasTarget", {}).get("DNSName", "").rstrip(".") != state["distribution_domain"].rstrip(".") for item in existing):
            raise RuntimeError("Existing site DNS differs; refusing to overwrite it.")
    else:
        change_records(state, aliases, "site_dns_change_id")
    state["site_dns_published"] = True
    save(state)
    print("Activated site A/AAAA aliases.")


def publication_status(state):
    if not state.get("invalidation_id"):
        raise RuntimeError("No publication is recorded.")
    state["invalidation_status"] = aws("cloudfront", "get-invalidation", "--distribution-id", state["distribution_id"], "--id", state["invalidation_id"])["Invalidation"]["Status"]
    save(state)
    print(json.dumps({key: state.get(key) for key in ["published_sha256", "published_at", "invalidation_id", "invalidation_status", "site_dns_published"]}, indent=2))


def http_request(hostname, path="/", secure=True, method="GET"):
    connection_class = http.client.HTTPSConnection if secure else http.client.HTTPConnection
    connection = connection_class(hostname, timeout=20)
    try:
        connection.request(method, path, headers={"Accept-Encoding": "identity", "User-Agent": "reptends-deployment-check/1.0"})
        response = connection.getresponse()
        return response.status, dict(response.getheaders()), response.read()
    finally:
        connection.close()


@contextmanager
def scoped_resolution(hostname, address):
    """Override one hostname in this short-lived CLI process, retaining TLS SNI."""
    if not address:
        yield
        return
    address = str(ipaddress.ip_address(address))
    original = socket.getaddrinfo

    def resolve(host, *arguments, **keywords):
        return original(address if host == hostname else host, *arguments, **keywords)

    socket.getaddrinfo = resolve
    try:
        yield
    finally:
        socket.getaddrinfo = original


def verify_site(state, target, resolve_ip=None):
    if not state.get("published_sha256"):
        raise RuntimeError("No publication has been recorded.")
    if target == "live" and not state.get("site_dns_published"):
        raise RuntimeError("Public DNS has not been activated.")
    hostname = DOMAIN if target == "live" else state["distribution_domain"]
    evidence = {"hostname": hostname, "verified_at": now(), "sha256": state["published_sha256"], "https": {}}
    if resolve_ip:
        evidence["process_only_dns_override"] = str(ipaddress.ip_address(resolve_ip))
    with scoped_resolution(hostname, resolve_ip):
        for path in ["/", "/index.html"]:
            status_code, headers, body = http_request(hostname, path)
            digest = hashlib.sha256(body).hexdigest()
            if status_code != 200 or digest != state["published_sha256"]:
                raise RuntimeError(f"HTTPS verification failed for {hostname}{path}: status {status_code}, body SHA-256 {digest}")
            if not any(key.lower() == "content-type" and value.lower().startswith("text/html") for key, value in headers.items()):
                raise RuntimeError("Published response is missing its HTML content type.")
            evidence["https"][path] = {"status": status_code, "sha256": digest}
        redirect_status, redirect_headers, _ = http_request(hostname, secure=False)
    location = next((value for key, value in redirect_headers.items() if key.lower() == "location"), "")
    if redirect_status not in [301, 302, 307, 308] or location != f"https://{hostname}/":
        raise RuntimeError("HTTP does not redirect to the expected HTTPS URL.")
    s3_status, _, _ = http_request(f"{BUCKET}.s3.{REGION}.amazonaws.com", "/index.html", method="HEAD")
    if s3_status != 403:
        raise RuntimeError(f"Expected anonymous S3 denial, received {s3_status}.")
    evidence.update(http_redirect_status=redirect_status, http_redirect_location=location, anonymous_s3_status=s3_status)
    state[target + "_verified_sha256"] = state["published_sha256"]
    state[target + "_verified_at"] = evidence["verified_at"]
    save(state)
    atomic_json(DIRECTORY / (target + "-verification.json"), evidence)
    print(json.dumps(evidence, indent=2))


def check_publishing_permissions(state, administrator_profile, custom=False):
    index = f"arn:aws:s3:::{BUCKET}/index.html"
    other = f"arn:aws:s3:::{BUCKET}/other.html"
    checks = [
        ("s3:PutObject", index, "allowed"),
        ("s3:PutObject", other, "implicitDeny"),
        ("s3:DeleteObject", index, "implicitDeny"),
        ("cloudfront:CreateInvalidation", state["distribution_arn"], "allowed"),
        ("cloudfront:GetInvalidation", state["distribution_arn"], "allowed"),
        ("cloudfront:CreateInvalidation", f"arn:aws:cloudfront::{ACCOUNT}:distribution/EOTHEREXAMPLE", "implicitDeny"),
        ("route53:ChangeResourceRecordSets", f"arn:aws:route53:::hostedzone/{ZONE}", "implicitDeny"),
        ("cloudfront:CreateDistribution", "*", "implicitDeny"),
        ("iam:CreateUser", f"arn:aws:iam::{ACCOUNT}:user/other", "implicitDeny")
    ]
    if custom:
        operation = "simulate-custom-policy"
        parameters = ["--policy-input-list", (DIRECTORY / "publisher-policy.json").read_text()]
    else:
        operation = "simulate-principal-policy"
        parameters = ["--policy-source-arn", f"arn:aws:iam::{ACCOUNT}:user/reptends-deployer"]
    evidence = []
    for action, resource, expected in checks:
        result = aws("iam", operation, *parameters, "--action-names", action,
                     "--resource-arns", resource, profile=administrator_profile)["EvaluationResults"][0]
        if result["EvalDecision"] != expected:
            raise RuntimeError(f"Permission check {action} on {resource}: expected {expected}, received {result['EvalDecision']}")
        evidence.append({"action": action, "resource": resource, "decision": result["EvalDecision"]})
    atomic_json(DIRECTORY / ("publisher-policy-checks.json" if custom else "publisher-effective-permissions.json"), {"verified_at": now(), "checks": evidence})
    print(f"Passed {len(checks)} {'custom-policy' if custom else 'effective-policy'} permission simulations.")


def narrow_permissions(state, administrator_profile):
    if not state.get("published_sha256") or state.get("live_verified_sha256") != state["published_sha256"]:
        raise RuntimeError("Verify the current publication at the live hostname before narrowing permissions.")
    administrator = aws("sts", "get-caller-identity", profile=administrator_profile)
    if administrator["Account"] != ACCOUNT:
        raise RuntimeError("Administrator profile is in another account.")
    user = "reptends-deployer"
    bootstrap = f"arn:aws:iam::{ACCOUNT}:policy/ReptendsBootstrap"
    publisher = f"arn:aws:iam::{ACCOUNT}:policy/ReptendsPublish"
    attached = aws("iam", "list-attached-user-policies", "--user-name", user, profile=administrator_profile)["AttachedPolicies"]
    if any(policy["PolicyArn"] not in [bootstrap, publisher] for policy in attached):
        raise RuntimeError("Unexpected attached policy; inspect before narrowing.")
    if aws("iam", "list-user-policies", "--user-name", user, profile=administrator_profile)["PolicyNames"] or aws("iam", "list-groups-for-user", "--user-name", user, profile=administrator_profile)["Groups"]:
        raise RuntimeError("Unexpected inline or group permissions; inspect before narrowing.")
    desired = json.loads((DIRECTORY / "publisher-policy.json").read_text())
    try:
        version = aws("iam", "get-policy", "--policy-arn", publisher, profile=administrator_profile)["Policy"]["DefaultVersionId"]
    except RuntimeError as error:
        if "(NoSuchEntity)" not in str(error):
            raise
        aws("iam", "create-policy", "--policy-name", "ReptendsPublish", "--policy-document", json_argument(desired), profile=administrator_profile)
        state["publisher_policy_arn"] = publisher
        save(state)
    else:
        actual = aws("iam", "get-policy-version", "--policy-arn", publisher, "--version-id", version, profile=administrator_profile)["PolicyVersion"]["Document"]
        if actual != desired:
            raise RuntimeError("Existing ReptendsPublish policy differs; refusing to overwrite it.")
    aws("iam", "attach-user-policy", "--user-name", user, "--policy-arn", publisher, profile=administrator_profile)
    state["publisher_policy_arn"] = publisher
    state["publisher_policy_attached"] = True
    save(state)
    if any(policy["PolicyArn"] == bootstrap for policy in attached):
        aws("iam", "detach-user-policy", "--user-name", user, "--policy-arn", bootstrap, profile=administrator_profile)
    state["bootstrap_policy_detached"] = True
    state["permissions_narrowed_at"] = now()
    save(state)
    check_publishing_permissions(state, administrator_profile)
    print("ReptendsPublish is attached and ReptendsBootstrap is detached; access key unchanged.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    configure = sub.add_parser("configure-profile")
    configure.add_argument("--credentials-csv", type=Path, required=True)
    sub.add_parser("provision")
    sub.add_parser("status")
    sub.add_parser("publication-status")
    verification = sub.add_parser("verify")
    verification.add_argument("--target", choices=["cloudfront", "live"], required=True)
    verification.add_argument("--resolve-ip", help="Use a separately verified public DNS answer for this process only; TLS hostname checks remain enabled.")
    permission_check = sub.add_parser("check-publisher-policy")
    permission_check.add_argument("--admin-profile", default="default")
    narrowing = sub.add_parser("narrow-permissions")
    narrowing.add_argument("--admin-profile", default="default")
    publication = sub.add_parser("publish")
    publication.add_argument("html", type=Path)
    publication.add_argument("--qa-passed", action="store_true")
    activation = sub.add_parser("activate-dns")
    activation.add_argument("--qa-passed", action="store_true")
    arguments = parser.parse_args()
    with (DIRECTORY / ".hosting.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if arguments.command == "configure-profile":
            configure_profile(arguments.credentials_csv)
            return
        state = load_state()
        if arguments.command == "provision":
            provision(state)
        elif arguments.command == "status":
            status(state)
        elif arguments.command == "publish":
            publish(state, arguments.html, arguments.qa_passed)
        elif arguments.command == "activate-dns":
            activate_dns(state, arguments.qa_passed)
        elif arguments.command == "publication-status":
            publication_status(state)
        elif arguments.command == "verify":
            verify_site(state, arguments.target, arguments.resolve_ip)
        elif arguments.command == "check-publisher-policy":
            check_publishing_permissions(state, arguments.admin_profile, custom=True)
        elif arguments.command == "narrow-permissions":
            narrow_permissions(state, arguments.admin_profile)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, KeyError, ValueError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
