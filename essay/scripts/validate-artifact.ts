/** Reject accidental credentials or runtime asset dependencies before publishing. */
export function assertPublishableHtml(html: string, css: string): void {
  const credentialPatterns = credentialPatternList();
  if (credentialPatterns.some(pattern => pattern.test(html))) {
    throw new Error("The page contains a credential pattern; the artifact was not written.");
  }

  // Scholarly reference links may leave the page; rendering must remain offline.
  if (/<(?:script|iframe)\b[^>]*\bsrc\s*=/i.test(html)
    || /<link\b[^>]*\brel\s*=\s*["']?(?:stylesheet|preload|modulepreload)\b/i.test(html)
    || /<(?:img|source|video|audio|input|embed)\b[^>]*\bsrc\s*=\s*["'](?!data:)/i.test(html)
    || /<(?:img|source)\b[^>]*\bsrcset\s*=/i.test(html)
    || /<(?:object)\b[^>]*\bdata\s*=\s*["'](?!data:)/i.test(html)
    || /url\(\s*["']?(?!data:|#)[^\s)"']/i.test(css)
    || /@import\b/i.test(css)) {
    throw new Error("The standalone page contains an external asset reference.");
  }
}

export function assertPublishableRobots(robots: string): void {
  if (!/^User-agent:\s*\*$/m.test(robots) || !/^Allow:\s*\/$/m.test(robots)) {
    throw new Error("robots.txt must explicitly allow all standards-respecting crawlers.");
  }
  if (/^Disallow:/im.test(robots)) {
    throw new Error("robots.txt must not contain a Disallow rule.");
  }
  if (credentialPatternList().some(pattern => pattern.test(robots))) {
    throw new Error("robots.txt contains a credential pattern; the artifact was not written.");
  }
}

function credentialPatternList(): RegExp[] {
  return [
    /\b(?:AKIA|ASIA)[A-Z0-9]{16}\b/,
    /(?:aws_secret_access_key|secretAccessKey)["']?\s*[:=]\s*["']?[A-Za-z0-9/+=]{40}(?![A-Za-z0-9/+=])/i,
    /-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----/,
    /Access key ID\s*,\s*Secret access key/i,
  ];
}
