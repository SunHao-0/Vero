#!/usr/bin/env python3
"""Build the Vero site and serve it locally for review.

    python3 scripts/serve_site.py [--port 8000] [--no-build] [--repo-url URL]

Serves on 127.0.0.1 only. Ctrl-C to stop.
"""
import argparse
import functools
import http.server
import socketserver
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "site"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--no-build", action="store_true", help="serve the existing site/")
    ap.add_argument("--repo-url", default="")
    args = ap.parse_args()

    if not args.no_build:
        subprocess.run([sys.executable, str(ROOT / "scripts" / "build_site.py"),
                        "--repo-url", args.repo_url], check=True)
    if not (SITE / "index.html").exists():
        sys.exit("site/ not built; run without --no-build first")

    handler = functools.partial(http.server.SimpleHTTPRequestHandler,
                                directory=str(SITE))
    # allow_reuse_address avoids "address already in use" on quick restarts.
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("127.0.0.1", args.port), handler) as httpd:
        print(f"serving {SITE} at http://127.0.0.1:{args.port}/  (Ctrl-C to stop)")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nstopped")


if __name__ == "__main__":
    main()
