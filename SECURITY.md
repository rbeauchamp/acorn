# Security reporting

Use GitHub's private vulnerability reporting for
[rbeauchamp/acorn](https://github.com/rbeauchamp/acorn/security/advisories/new):
Security → Advisories → Report a vulnerability. Richard Beauchamp is the
responsible maintainer. Keep vulnerability details, credentials and private run
data in the private report.

Include the affected revision, impact, relevant code paths, assumptions and the
smallest safe reproduction or reasoning needed to assess the report. Avoid
accessing other people's systems or data.

Run the viewer on loopback and keep its run directory accessible only to the
local operator. Keep it behind that local boundary when handling sensitive run
data. Operator-supplied commands execute with the operator's permissions.

GitHub private vulnerability reporting is available while the repository is
public. During private development, repository collaborators can use a private
issue to contact the maintainer.
