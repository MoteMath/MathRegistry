"""Install the published mreg client in a private, per-user environment."""
import argparse
import hashlib
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
import venv

VERSION = "__MREG_VERSION__"
CLIENT_SHA256 = "__MREG_SHA256__"
DEFAULT_BASE = "https://mathregistry.com"


def download(base):
    parsed = urllib.parse.urlsplit(base)
    local = parsed.scheme == "http" and parsed.hostname in ("127.0.0.1", "localhost", "::1")
    if (parsed.scheme != "https" and not local) or parsed.username or parsed.password or parsed.query or parsed.fragment:
        raise ValueError("Use an HTTPS download URL or a loopback test server")
    url = base.rstrip("/") + "/downloads/mreg-" + VERSION + ".py"
    with urllib.request.urlopen(url, timeout=60) as response:
        data = response.read(8 * 1024 * 1024 + 1)
    if hashlib.sha256(data).hexdigest() != CLIENT_SHA256:
        raise ValueError("Client checksum mismatch. The installed mreg was left in place.")
    compile(data, "mreg.py", "exec")
    return data


def ensure_zstd(python):
    probe = "import importlib.util,shutil; assert importlib.util.find_spec('compression') and importlib.util.find_spec('compression.zstd') or importlib.util.find_spec('zstandard') or shutil.which('zstd')"
    if subprocess.run([str(python), "-c", probe], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
        return
    subprocess.run([str(python), "-m", "ensurepip"], check=True)
    subprocess.run([str(python), "-m", "pip", "install", "--disable-pip-version-check", "zstandard"], check=True)


def add_to_path(bin_dir):
    if os.name == "nt":
        import winreg
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, "Environment") as key:
            try:
                current, kind = winreg.QueryValueEx(key, "Path")
            except FileNotFoundError:
                current, kind = "", winreg.REG_EXPAND_SZ
            if str(bin_dir).casefold() not in [p.casefold() for p in current.split(";")]:
                winreg.SetValueEx(key, "Path", 0, kind, current.rstrip(";") + ";" + str(bin_dir))
        return
    shell = Path(os.environ.get("SHELL", "/bin/sh")).name
    profiles = [Path.home() / ".profile"]
    if shell == "bash":
        profiles.append(Path.home() / ".bashrc")
        if (Path.home() / ".bash_profile").exists():
            profiles.append(Path.home() / ".bash_profile")
    elif shell == "zsh":
        profiles.append(Path.home() / ".zshrc")
    elif shell == "fish":
        profiles = [Path.home() / ".config/fish/conf.d/mreg.fish"]
    line = "fish_add_path " + shlex.quote(str(bin_dir)) if shell == "fish" else "export PATH=" + shlex.quote(str(bin_dir)) + ':"$PATH"'
    for profile in profiles:
        existing = profile.read_text() if profile.exists() else ""
        if line not in existing.splitlines():
            profile.parent.mkdir(parents=True, exist_ok=True)
            with profile.open("a") as stream:
                stream.write("\n# mreg command\n" + line + "\n")


def install(base, prefix, bin_dir, update_path=True):
    if sys.version_info < (3, 10):
        raise RuntimeError("mreg needs Python 3.10 or newer")
    data = download(base)
    prefix, bin_dir = Path(prefix).resolve(), Path(bin_dir).resolve()
    prefix.mkdir(parents=True, exist_ok=True)
    bin_dir.mkdir(parents=True, exist_ok=True)
    # Each attempt owns its environment. Concurrent installs and failures cannot
    # change the environment behind an already installed launcher.
    release = Path(tempfile.mkdtemp(prefix="release-" + VERSION + "-", dir=prefix))
    activated = False
    temporary = None
    try:
        venv.EnvBuilder(with_pip=False).create(release)
        python = release / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
        client = release / "mreg.py"
        client.write_bytes(data)
        ensure_zstd(python)
        subprocess.run([str(python), str(client), "--help"], check=True, stdout=subprocess.DEVNULL)
        launcher = bin_dir / ("mreg.cmd" if os.name == "nt" else "mreg")
        if os.name == "nt":
            command = '@echo off\nsetlocal DisableDelayedExpansion\n"' + str(python).replace('%', '%%') + '" "' + str(client).replace('%', '%%') + '" %*\n'
        else:
            command = "#!/bin/sh\nexec " + shlex.quote(str(python)) + " " + shlex.quote(str(client)) + ' "$@"\n'
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n", dir=bin_dir, prefix=".mreg-", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(command)
        temporary.chmod(0o755)
        os.replace(temporary, launcher)
        activated = True
        if update_path:
            add_to_path(bin_dir)
        print("Installed mreg " + VERSION + " at " + str(launcher))
        print("Open a new terminal and run mreg login.")
        print("For this terminal, run " + str(launcher) + " login")
        return launcher
    finally:
        if temporary and temporary.exists():
            temporary.unlink()
        if not activated and release.resolve().parent == prefix and release.name.startswith("release-"):
            shutil.rmtree(release)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-url", default=DEFAULT_BASE)
    parser.add_argument("--prefix", default=os.environ.get("MREG_INSTALL_DIR", str(Path.home() / ".local/share/mreg")))
    parser.add_argument("--bin-dir", default=os.environ.get("MREG_BIN_DIR", str(Path.home() / ".local/bin")))
    parser.add_argument("--no-path", action="store_true", default=os.environ.get("MREG_NO_MODIFY_PATH") == "1")
    args = parser.parse_args()
    try:
        install(args.base_url, args.prefix, args.bin_dir, not args.no_path)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print("mreg installer: " + str(error), file=sys.stderr)
        print("On Debian or Ubuntu, install python3-venv if environment creation failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
