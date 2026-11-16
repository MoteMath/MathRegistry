#!/bin/sh
set -eu
python_command=""
for candidate in python3 python; do
    if command -v "$candidate" >/dev/null 2>&1 && "$candidate" -c 'import sys; sys.exit(sys.version_info < (3, 10))' 2>/dev/null; then
        python_command="$candidate"
        break
    fi
done
if [ -z "$python_command" ]; then
    echo 'mreg needs Python 3.10 or newer. Install Python and run this command again.' >&2
    exit 1
fi
base_url="${MREG_INSTALL_BASE_URL:-https://mathregistry.com}"
installer_file="$(mktemp)"
trap 'rm -f "$installer_file"' EXIT HUP INT TERM
curl --fail --silent --show-error --location "$base_url/downloads/install.py" --output "$installer_file"
"$python_command" "$installer_file" --base-url "$base_url"
