#!/bin/sh
# Compiles linreg.bend to JavaScript and inlines it into page.html, writing
#   ../docs/index.html  a standalone page (GitHub Pages serves it)
#   artifact.html       the same page without the document shell, for claude.ai
set -e
cd "$(dirname "$0")"
bend ../linreg.bend -o linreg.mjs
mkdir -p ../docs
python3 - <<'EOF'
mod = open("linreg.mjs").read().replace("export default {", "return {", 1)
page = open("page.html").read().replace("/*BEND_MODULE*/", mod, 1)
open("artifact.html", "w").write(page)

head, body = page.split("</style>\n", 1)
head = "\n".join(l for l in head.splitlines() if "claude:viewport-fit-sides" not in l)
open("../docs/index.html", "w").write(f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="description" content="Least squares with exact fractions, written in Bend and running in the browser.">
{head}
[hidden]{{display:none!important}}
</style>
</head>
<body>
{body}</body>
</html>
""")
EOF
rm linreg.mjs
echo "wrote docs/index.html and web/artifact.html"
