"""Serve the site locally, with an API for editing papers from the bibliography page.

Usage: python scripts/serve.py [port]        (default port 8765, http://localhost:8765)

GET  /api/status         -> {"editable": true}; the edit forms show working Save buttons only then.
POST /api/papers/<id>    -> body: the paper as JSON (same fields as data/papers/<id>.yaml).
                            The entry is checked against schema/paper.schema.json and against the
                            existing authors and venues, written to data/papers/<id>.yaml, and the
                            site is rebuilt (site/data.js and the asset versions in the pages).
POST /api/results/<id>   -> the same for a result: checked against schema/result.schema.json, the
                            existing papers and the year of the earliest source, then written to
                            data/results/<id>.yaml.

Only existing entries can be edited (id and problem stay), and the server only listens on localhost.
"""
import json
import re
import sys
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import yaml
from jsonschema import Draft202012Validator

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_site  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
PAPER_SCHEMA = json.loads((ROOT / "schema" / "paper.schema.json").read_text(encoding="utf-8"))
RESULT_SCHEMA = json.loads((ROOT / "schema" / "result.schema.json").read_text(encoding="utf-8"))
FIELD_ORDER = ["id", "label", "title", "authors", "public_url", "versions"]
VERSION_ORDER = ["type", "venue", "year", "title", "doi", "arxiv", "url"]
RESULT_ORDER = list(RESULT_SCHEMA["properties"])          # id, title, problem, ... status
SOURCE_ORDER = ["paper", "reference", "url"]


def load(folder):
    return {p.stem: yaml.safe_load(p.read_text(encoding="utf-8")) for p in (ROOT / "data" / folder).glob("*.yaml")}


def clean(paper):
    """Drop empty optional fields and put the keys in the usual order."""
    out = {k: paper[k] for k in FIELD_ORDER if paper.get(k) not in (None, "", [])}
    out["versions"] = [{k: v[k] for k in VERSION_ORDER if v.get(k) not in (None, "")}
                       for v in paper.get("versions", [])]
    return out


def check(paper, pid):
    """Return a list of problems with the edited paper (empty if it can be saved)."""
    errors = [f"{'/'.join(map(str, e.absolute_path)) or '(root)'}: {e.message}"
              for e in Draft202012Validator(PAPER_SCHEMA, format_checker=Draft202012Validator.FORMAT_CHECKER)
              .iter_errors(paper)]
    if paper.get("id") != pid:
        errors.append(f"id must stay '{pid}'")
    authors, venues = load("authors"), load("venues")
    for a in paper.get("authors", []):
        if a not in authors:
            errors.append(f"unknown author '{a}'")
    for v in paper.get("versions", []):
        venue = venues.get(v.get("venue"))
        if venue is None:
            errors.append(f"unknown venue '{v.get('venue')}'")
        elif venue["type"] != v.get("type"):
            errors.append(f"venue '{v['venue']}' is a {venue['type']}, not a {v.get('type')}")
    return errors


def schema_errors(schema, entry):
    return [f"{'/'.join(map(str, e.absolute_path)) or '(root)'}: {e.message}"
            for e in Draft202012Validator(schema, format_checker=Draft202012Validator.FORMAT_CHECKER).iter_errors(entry)]


def clean_result(result):
    """Drop empty optional fields and put the keys in schema order."""
    out = {k: result[k] for k in RESULT_ORDER if result.get(k) not in (None, "", [], {})}
    out["sources"] = [{k: s[k] for k in SOURCE_ORDER if s.get(k) not in (None, "")}
                      for s in result.get("sources", [])]
    return out


def check_result(result, rid, current):
    errors = schema_errors(RESULT_SCHEMA, result)
    if result.get("id") != rid:
        errors.append(f"id must stay '{rid}'")
    if result.get("problem") != current.get("problem"):
        errors.append(f"problem must stay '{current.get('problem')}'")
    if result.get("problem") in ("vertex-coloring", "edge-coloring") and "colors" not in result:
        errors.append("coloring results need colors")
    if result.get("problem") == "network-decomposition" and "decomposition" not in result:
        errors.append("network decomposition results need colors and diameter")
    papers = load("papers")
    years = []
    for s in result.get("sources", []):
        if s.get("paper") not in papers:
            errors.append(f"unknown paper '{s.get('paper')}'")
        else:
            years.append(min(v["year"] for v in papers[s["paper"]]["versions"]))
    if years and isinstance(result.get("year"), int) and result["year"] < min(years):
        errors.append(f"year {result['year']} is before all of its sources ({min(years)})")
    return errors


class Handler(SimpleHTTPRequestHandler):
    def _json(self, status, body):
        data = json.dumps(body).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if self.path == "/api/status":
            return self._json(200, {"editable": True})
        return super().do_GET()

    def _body(self):
        return json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")

    def _save_result(self, rid):
        target = ROOT / "data" / "results" / f"{rid}.yaml"
        if not target.exists():
            return self._json(404, {"errors": [f"no result '{rid}'"]})
        try:
            result = clean_result(self._body())
        except (ValueError, AttributeError, TypeError) as e:
            return self._json(400, {"errors": [f"invalid request: {e}"]})
        current = yaml.safe_load(target.read_text(encoding="utf-8"))
        errors = check_result(result, rid, current)
        if errors:
            return self._json(400, {"errors": errors})
        target.write_text(yaml.safe_dump(result, allow_unicode=True, sort_keys=False, width=1000),
                          encoding="utf-8", newline="\n")
        build_site.main()
        return self._json(200, {"saved": f"data/results/{rid}.yaml"})

    def do_POST(self):
        m = re.fullmatch(r"/api/results/([a-z0-9]+(?:-[a-z0-9]+)*)", self.path)
        if m:
            return self._save_result(m.group(1))
        m = re.fullmatch(r"/api/papers/([a-z0-9]+(?:-[a-z0-9]+)*)", self.path)
        if not m:
            return self._json(404, {"errors": ["unknown endpoint"]})
        pid = m.group(1)
        target = ROOT / "data" / "papers" / f"{pid}.yaml"
        if not target.exists():
            return self._json(404, {"errors": [f"no paper '{pid}'"]})
        try:
            paper = clean(json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}"))
        except (ValueError, AttributeError, TypeError) as e:
            return self._json(400, {"errors": [f"invalid request: {e}"]})
        errors = check(paper, pid)
        if errors:
            return self._json(400, {"errors": errors})
        target.write_text(yaml.safe_dump(paper, allow_unicode=True, sort_keys=False, width=1000),
                          encoding="utf-8", newline="\n")
        build_site.main()
        return self._json(200, {"saved": f"data/papers/{pid}.yaml"})


class Server(ThreadingHTTPServer):
    # On Windows, address reuse would let a second server share the port silently (and answer with old
    # code); without it, starting a second copy fails with "address already in use".
    allow_reuse_address = False


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
    server = Server(("127.0.0.1", port), partial(Handler, directory=str(SITE)))
    print(f"Serving {SITE} at http://localhost:{port} (paper editing enabled)")
    server.serve_forever()


if __name__ == "__main__":
    main()
