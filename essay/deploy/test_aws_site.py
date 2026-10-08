"""Tests for deployment safety boundaries; no AWS requests are made."""
import configparser
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import aws_site as site


class DeploymentSafetyTests(unittest.TestCase):
    def migration_state(self):
        return {"published_sha256": "reviewed", "live_verified_sha256": "reviewed",
                "distribution_arn": "arn:aws:cloudfront::341982967115:distribution/example"}

    def migration_aws(self, unexpected_bucket=False, unexpected_iam=False):
        calls = []
        state = self.migration_state()
        publisher = f"arn:aws:iam::{site.ACCOUNT}:policy/ReptendsPublish"

        def response(service, operation, *arguments, **kwargs):
            calls.append((service, operation, arguments))
            if (service, operation) == ("sts", "get-caller-identity"):
                return {"Account": site.ACCOUNT}
            if operation == "list-attached-user-policies":
                return {"AttachedPolicies": [{"PolicyArn": publisher}]}
            if operation == "list-user-policies":
                return {"PolicyNames": []}
            if operation == "list-groups-for-user":
                return {"Groups": []}
            if operation == "get-public-access-block":
                return {"PublicAccessBlockConfiguration": {flag: True for flag in
                    ["BlockPublicAcls", "IgnorePublicAcls", "BlockPublicPolicy", "RestrictPublicBuckets"]}}
            if operation == "get-bucket-policy":
                policy = {"Version": "unexpected"} if unexpected_bucket else site.legacy_index_bucket_policy(state["distribution_arn"])
                return {"Policy": json.dumps(policy)}
            if operation == "get-policy":
                return {"Policy": {"DefaultVersionId": "v1"}}
            if operation == "get-policy-version":
                policy = {"Version": "unexpected"} if unexpected_iam else site.legacy_index_publisher_policy(state["distribution_arn"])
                return {"PolicyVersion": {"Document": policy}}
            if operation == "list-policy-versions":
                return {"Versions": [{"VersionId": "v1", "IsDefaultVersion": True}]}
            if operation == "simulate-principal-policy":
                action = arguments[arguments.index("--action-names") + 1]
                resource = arguments[arguments.index("--resource-arns") + 1]
                allowed = ((action == "s3:PutObject" and resource in
                            {site.object_arn("index.html"), site.object_arn("robots.txt")}) or
                           (action in {"cloudfront:CreateInvalidation", "cloudfront:GetInvalidation"} and
                            resource == state["distribution_arn"]))
                return {"EvaluationResults": [{"EvalDecision": "allowed" if allowed else "implicitDeny"}]}
            return {}

        return state, calls, response

    def test_publish_and_dns_require_explicit_qa(self):
        with patch.object(site, "aws") as aws:
            with self.assertRaisesRegex(RuntimeError, "--qa-passed"):
                site.publish({}, Path("missing.html"), False)
            with self.assertRaisesRegex(RuntimeError, "--qa-passed"):
                site.activate_dns({}, False)
            aws.assert_not_called()

    def test_publish_uploads_robots_before_the_reviewed_html(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            html = folder / "index.html"
            robots = folder / "robots.txt"
            html.write_text("<!doctype html><title>Test</title>")
            robots.write_text("User-agent: *\nAllow: /\n")
            state = {"ready_for_qa_gated_publish": True, "distribution_id": "distribution"}

            def response(service, operation, *arguments, **kwargs):
                if operation == "create-invalidation":
                    return {"Invalidation": {"Id": "invalidation", "Status": "InProgress"}}
                return {}

            with patch.object(site, "identity"), patch.object(site, "save"), \
                    patch.object(site, "aws", side_effect=response) as aws:
                site.publish(state, html, True)

            uploads = [call.args for call in aws.call_args_list if call.args[1] == "put-object"]
            self.assertEqual([call[call.index("--key") + 1] for call in uploads], ["robots.txt", "index.html"])
            self.assertEqual(state["published_assets"]["index.html"]["bytes"], len(html.read_bytes()))
            self.assertEqual(state["published_assets"]["robots.txt"]["bytes"], len(robots.read_bytes()))

    def test_publish_rejects_a_disallowing_robots_policy(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            html = folder / "index.html"
            robots = folder / "robots.txt"
            html.write_text("<!doctype html><title>Test</title>")
            robots.write_text("User-agent: *\nDisallow: /private\nAllow: /\n")
            state = {"ready_for_qa_gated_publish": True, "distribution_id": "distribution"}
            with patch.object(site, "identity"), patch.object(site, "aws") as aws:
                with self.assertRaisesRegex(RuntimeError, "Disallow"):
                    site.publish(state, html, True)
                aws.assert_not_called()

    def test_publication_policies_allow_only_the_two_public_objects(self):
        distribution = "arn:aws:cloudfront::341982967115:distribution/example"
        expected = {site.object_arn("index.html"), site.object_arn("robots.txt")}
        bucket = site.desired_bucket_policy(distribution)
        publisher = site.desired_publisher_policy(distribution)
        self.assertEqual(set(bucket["Statement"][0]["Resource"]), expected)
        self.assertEqual(set(publisher["Statement"][0]["Resource"]), expected)
        self.assertEqual(bucket["Statement"][0]["Condition"]["StringEquals"]["AWS:SourceArn"], distribution)

    def test_narrowing_migrates_only_the_exact_legacy_policies(self):
        state, calls, response = self.migration_aws()
        with patch.object(site, "aws", side_effect=response), patch.object(site, "save"), \
                patch.object(site, "atomic_json"):
            site.narrow_permissions(state, "default")
        operations = [operation for _, operation, _ in calls]
        self.assertIn("put-bucket-policy", operations)
        self.assertIn("create-policy-version", operations)
        create = next(arguments for _, operation, arguments in calls if operation == "create-policy-version")
        self.assertIn("--set-as-default", create)

    def test_narrowing_refuses_an_unexpected_bucket_policy_without_mutation(self):
        state, calls, response = self.migration_aws(unexpected_bucket=True)
        with patch.object(site, "aws", side_effect=response), patch.object(site, "save"), \
                patch.object(site, "atomic_json"):
            with self.assertRaisesRegex(RuntimeError, "neither the reviewed legacy policy"):
                site.narrow_permissions(state, "default")
        operations = [operation for _, operation, _ in calls]
        self.assertNotIn("put-bucket-policy", operations)
        self.assertNotIn("create-policy-version", operations)

    def test_narrowing_inspects_both_policies_before_any_mutation(self):
        state, calls, response = self.migration_aws(unexpected_iam=True)
        with patch.object(site, "aws", side_effect=response), patch.object(site, "save"), \
                patch.object(site, "atomic_json"):
            with self.assertRaisesRegex(RuntimeError, "ReptendsPublish policy is neither"):
                site.narrow_permissions(state, "default")
        operations = [operation for _, operation, _ in calls]
        self.assertNotIn("put-bucket-policy", operations)
        self.assertNotIn("create-policy-version", operations)

    def test_dns_requires_cloudfront_verification(self):
        with patch.object(site, "aws") as aws:
            with self.assertRaisesRegex(RuntimeError, "Verify the published"):
                site.activate_dns({"published_sha256": "approved"}, True)
            aws.assert_not_called()

    def test_narrowing_requires_live_verification(self):
        with patch.object(site, "aws") as aws:
            with self.assertRaisesRegex(RuntimeError, "live hostname"):
                site.narrow_permissions({"published_sha256": "new", "live_verified_sha256": "old"}, "default")
            aws.assert_not_called()

    def test_scoped_resolution_retains_other_hosts_and_restores_resolver(self):
        with patch.object(site.socket, "getaddrinfo", return_value=[]) as original:
            with site.scoped_resolution(site.DOMAIN, "192.0.2.1"):
                site.socket.getaddrinfo(site.DOMAIN, 443)
                original.assert_called_with("192.0.2.1", 443)
                site.socket.getaddrinfo("other.example", 443)
                original.assert_called_with("other.example", 443)
            self.assertIs(site.socket.getaddrinfo, original)

    def test_provision_validation_stage_does_not_publish_site(self):
        state = {"preflight_done": True, "bucket_created": True,
                 "bucket_configured": True, "certificate_arn": "certificate"}
        calls = []

        def aws(service, operation, *arguments, **kwargs):
            calls.append((service, operation, arguments))
            if operation == "describe-certificate":
                return {"Certificate": {"Status": "PENDING_VALIDATION", "DomainValidationOptions": [
                    {"ResourceRecord": {"Name": "_abc.reptends.mikedotexe.com.",
                                        "Type": "CNAME", "Value": "_abc.acm-validations.aws."}}]}}
            if operation == "change-resource-record-sets":
                return {"ChangeInfo": {"Id": "/change/test"}}
            raise AssertionError("Unexpected AWS call: " + operation)

        with patch.object(site, "identity"), patch.object(site, "save"), patch.object(site, "aws", side_effect=aws):
            site.provision(state)
        self.assertEqual([item[1] for item in calls], ["describe-certificate", "change-resource-record-sets"])
        self.assertNotIn('"Type":"A"', calls[1][2][-1])
        self.assertNotIn('"Type":"AAAA"', calls[1][2][-1])
        self.assertNotIn("published_sha256", state)

    def test_resume_uses_existing_resource_ids(self):
        state = {"preflight_done": True, "bucket_created": True, "bucket_configured": True,
                 "certificate_arn": "certificate", "certificate_dns_change_id": "/change/test",
                 "oac_id": "oac", "distribution_id": "distribution", "distribution_arn": "arn",
                 "bucket_policy_configured": True}
        with patch.object(site, "identity"), patch.object(site, "save"), patch.object(site, "status"), patch.object(site, "atomic_json"), patch.object(site, "aws", return_value={"Certificate": {"Status": "ISSUED"}}) as aws:
            site.provision(state)
        self.assertEqual(aws.call_count, 1)
        self.assertEqual(aws.call_args.args[1], "describe-certificate")

    def test_profile_update_preserves_other_profiles(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "config"
            original = "[default]\nregion = us-west-2\noutput = text\n\n[profile reptends]\nregion = old\n\n[profile other]\nregion = eu-west-1\n"
            path.write_text(original)
            before = configparser.ConfigParser()
            before.read_string(original)
            site.replace_ini_section(path, "profile reptends", {"region": "us-east-1", "output": "json"})
            after = configparser.ConfigParser()
            after.read(path)
            self.assertEqual(dict(before["default"]), dict(after["default"]))
            self.assertEqual(dict(before["profile other"]), dict(after["profile other"]))
            self.assertEqual(after["profile reptends"]["region"], "us-east-1")
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)


if __name__ == "__main__":
    unittest.main()
