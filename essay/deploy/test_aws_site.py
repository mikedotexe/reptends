"""Tests for deployment safety boundaries; no AWS requests are made."""
import configparser
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import aws_site as site


class DeploymentSafetyTests(unittest.TestCase):
    def test_publish_and_dns_require_explicit_qa(self):
        with patch.object(site, "aws") as aws:
            with self.assertRaisesRegex(RuntimeError, "--qa-passed"):
                site.publish({}, Path("missing.html"), False)
            with self.assertRaisesRegex(RuntimeError, "--qa-passed"):
                site.activate_dns({}, False)
            aws.assert_not_called()

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
