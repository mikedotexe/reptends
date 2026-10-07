# Reptends hosting

Run the commands below from the `essay/` directory of the repository (or the canonical local `physics-math-research/site` path).

The public site is a single built `dist/index.html` at <https://reptends.mikedotexe.com>.
AWS account `341982967115` owns a private S3 bucket in `us-east-1`, a CloudFront
distribution with signed origin access, an ACM certificate, and Route 53 records.
The bucket permits CloudFront to read only `index.html` and blocks public access.

`hosting.json` is the canonical, nonsecret record of resource IDs and completed
steps. Preserve it when resuming work. `distribution-config.json` and
`bucket-policy.json` record the created configuration. The script saves state
after every successful resource creation and uses a stable certificate token,
OAC name, and CloudFront caller reference to avoid duplicate infrastructure.

## Credentials

Use AWS CLI v2 and Python 3.10 or later. The `reptends` profile identifies the
dedicated IAM user `reptends-deployer`. Credentials belong in `~/.aws/credentials`,
never this directory, the HTML, or Git. Import the downloaded CSV without printing
its contents:

```sh
python3 deploy/aws_site.py configure-profile --credentials-csv /absolute/path/to/reptends-deployer_accessKeys.csv
```

This verifies the account and IAM user before updating only the `reptends`
sections of the AWS credentials and config files. Other profile values are
preserved. The configured region is `us-east-1`.

## Prepare infrastructure

```sh
python3 deploy/aws_site.py provision
```

Run this command again when it reports pending certificate validation. It resumes
completed steps, creates the ACM validation CNAME, then creates the OAC,
distribution, and private bucket policy once the certificate is issued. The
standard distribution uses GET/HEAD, HTTP-to-HTTPS redirects, SNI, IPv6,
compression, `index.html` as its default root object, and the managed
`CachingOptimized` policy. It contains no WAF, functions, tags, logging resources,
or VPC origin.

```sh
python3 deploy/aws_site.py status
```

This reports certificate, distribution, and DNS progress without blocking in a
long waiter. Check again after 20–60 seconds if deployment is still pending.
`ready_for_qa_gated_publish: true` means the infrastructure is ready. Provisioning
does **not** upload HTML or create the public site A/AAAA records.

If a resource creation response is lost, preserve the state and recover the
existing resource ID before continuing. An OAC marked `oac_create_pending` must
be reconciled by an administrator using its recorded name. A CloudFront
`DistributionAlreadyExists` error after interruption should be reconciled to the
distribution with the recorded caller reference, not retried with a new reference.
Certificate idempotency tokens last one hour; recover an existing requested
certificate if a response was lost outside that window.

## Publish after QA

Run the site's mathematical and browser checks first. `--qa-passed` records an
explicit operator decision; it does not execute those checks itself.

```sh
python3 deploy/aws_site.py publish dist/index.html --qa-passed
python3 deploy/aws_site.py publication-status
```

Publishing uploads only `index.html`, sends `Content-Type: text/html;
charset=utf-8` and `Cache-Control: max-age=60`, and invalidates `/*`. The file's
SHA-256 digest and publication time are saved. Recheck `publication-status` until
the invalidation is `Completed`. Before the first public DNS activation, verify
the content using the recorded CloudFront domain:

```sh
python3 deploy/aws_site.py verify --target cloudfront
```

Verification compares both `/` and `/index.html` to the uploaded SHA-256 digest,
checks their HTML content type and the HTTP-to-HTTPS redirect, and confirms the
private S3 object refuses anonymous requests. DNS activation requires this check.

For the first launch only, after verifying that uploaded content:

```sh
python3 deploy/aws_site.py activate-dns --qa-passed
python3 deploy/aws_site.py status
python3 deploy/aws_site.py verify --target live
```

This creates A and AAAA aliases in hosted zone `ZEBBWSGTKUUP6`, targeting the
recorded distribution. It refuses to overwrite conflicting records. Verify the
custom HTTPS URL, the HTTP redirect, and the private S3 URL's denial. Keep the ACM
validation CNAME so certificate renewal continues.

If the local resolver cached the previously nonexistent hostname, first verify
the new A/AAAA records against the authoritative Route 53 server and public
resolvers. Then pass one confirmed public A-record address to `verify --target
live --resolve-ip ADDRESS`. This overrides only that hostname inside the verifier
process; it retains the original HTTPS hostname, SNI, certificate verification,
and Host header. The override is recorded in the verification evidence. No system
DNS settings are changed.

## Reduce permissions after successful launch

`publisher-policy.json` contains the final policy with the actual distribution
ARN. After the live site checks pass, use the administrator profile to attach
`ReptendsPublish` and detach `ReptendsBootstrap`:

```sh
python3 deploy/aws_site.py check-publisher-policy --admin-profile default
python3 deploy/aws_site.py narrow-permissions --admin-profile default
python3 deploy/aws_site.py publication-status
```

The first command performs nine read-only IAM simulations. The second requires
successful verification of the currently published digest at the live hostname,
preserves unrelated policies, and checks effective permissions after the switch.
It stops on unexpected existing policies rather than editing them. Re-running it
resumes an interrupted policy attachment/detachment. The final policy grants
only `s3:PutObject` for this `index.html` and CloudFront invalidation creation and
status for this distribution. The access key does not change. Future publishing
and `publication-status` work with that policy; infrastructure `provision`,
`status`, and first-time DNS activation require bootstrap permissions.

## Tooling checks

```sh
python3 -m unittest discover -s deploy -p 'test_*.py'
```

AWS references: [private S3 origins and OAC](https://docs.aws.amazon.com/AmazonCloudFront/latest/DeveloperGuide/private-content-restricting-access-to-s3.html),
[CloudFront CLI tutorial](https://docs.aws.amazon.com/AmazonCloudFront/latest/DeveloperGuide/get-started-cli-tutorial.html),
[managed cache policies](https://docs.aws.amazon.com/AmazonCloudFront/latest/DeveloperGuide/using-managed-cache-policies.html),
[ACM requirements](https://docs.aws.amazon.com/AmazonCloudFront/latest/DeveloperGuide/cnames-and-https-requirements.html),
[Route 53 aliases](https://docs.aws.amazon.com/Route53/latest/DeveloperGuide/routing-to-cloudfront-distribution.html).
