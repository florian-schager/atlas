"""Link result sources to the theorem they cite, in the HTML version of the paper on arXiv.

Usage: python scripts/link_theorems.py [--dry-run]

For every source of a result or reduction that has a `reference` like "Theorem 1.3" (also Lemma,
Corollary, Proposition; a trailing remark in parentheses is ignored) and no `url` yet, and whose paper
has an arXiv `public_url`, the script fetches the paper's HTML version (arxiv.org/html, else ar5iv),
finds the element whose heading is exactly that theorem, and adds

    url: https://arxiv.org/html/<id>v<k>#<anchor>

to the source. The link names the arXiv version it was found in, since later versions may renumber.
References that cannot be matched are listed and left alone.
"""
import re
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
KINDS = "Theorem|Lemma|Corollary|Proposition|Claim|Definition"
NUMBER = r"(?:[A-Z](?:\.\d+)+|[A-Z]?\d+(?:\.\d+)*)"   # 3, 3.1, D.4, A.2.1
REF = re.compile(rf"^\s*({KINDS})\s+({NUMBER})\s*(?:\(.*\))?\s*$")
HEADERS = {"User-Agent": "atlas-of-distributed-algorithms/0.1 (theorem links)"}


def arxiv_id(paper):
    m = re.search(r"arxiv\.org/(?:abs|pdf|html)/([0-9]{4}\.[0-9]{4,5})", paper.get("public_url") or "")
    return m.group(1) if m else None


def fetch(url):
    """Return (final url, html) or (None, None)."""
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=HEADERS), timeout=60) as r:
            return r.geturl(), r.read().decode("utf-8", errors="replace")
    except (urllib.error.URLError, TimeoutError):
        return None, None


def latest_version(aid):
    """The newest arXiv version, e.g. "2410.19516v2", from the arXiv API."""
    _, feed = fetch(f"https://export.arxiv.org/api/query?id_list={aid}")
    m = re.search(rf"arxiv\.org/abs/({re.escape(aid)}v\d+)", feed or "")
    return m.group(1) if m else None


def html_version(aid):
    """The HTML page of the newest version on arxiv.org, else the ar5iv page."""
    version = latest_version(aid)
    if version:
        final, html = fetch(f"https://arxiv.org/html/{version}")
        if html and "ltx_theorem" in html:
            return f"https://arxiv.org/html/{version}", html
    final, html = fetch(f"https://ar5iv.labs.arxiv.org/html/{aid}")
    if html and "ltx_theorem" in html:
        return f"https://ar5iv.labs.arxiv.org/html/{aid}", html
    return None, None


def anchors(html):
    """Map "Theorem 1.3" -> element id, from the theorem headings of a LaTeXML page."""
    out = {}
    # The id comes before the class on arxiv.org and after it on ar5iv.
    tag = r'<div (?:id="([^"]+)" class="ltx_theorem[^"]*"|class="ltx_theorem[^"]*" id="([^"]+)")[^>]*>'
    for m in re.finditer(tag, html):
        text = re.sub(r"<[^>]+>", " ", html[m.end():m.end() + 600])
        head = re.match(rf"\s*({KINDS})\s+({NUMBER})", re.sub(r"\s+", " ", text))
        if head:
            out.setdefault(f"{head.group(1)} {head.group(2)}", m.group(1) or m.group(2))
    return out


def main():
    dry = "--dry-run" in sys.argv
    papers = {p.stem: yaml.safe_load(p.read_text(encoding="utf-8")) for p in (ROOT / "data" / "papers").glob("*.yaml")}
    todo = []   # (path, paper id, reference, normalized label)
    for folder in ("results", "reductions"):
        for path in sorted((ROOT / "data" / folder).glob("*.yaml")):
            entry = yaml.safe_load(path.read_text(encoding="utf-8"))
            for s in entry.get("sources") or []:
                m = REF.match(s.get("reference", ""))
                if m and not s.get("url") and arxiv_id(papers.get(s["paper"], {})):
                    todo.append((path, s["paper"], s["reference"], f"{m.group(1)} {m.group(2)}"))

    pages = {}
    linked, missed = [], []
    for path, pid, reference, label in todo:
        if pid not in pages:
            pages[pid] = html_version(arxiv_id(papers[pid]))
            time.sleep(3)   # be gentle with arxiv.org
        base, html = pages[pid]
        anchor = anchors(html).get(label) if html else None
        if not anchor:
            missed.append((path.stem, pid, reference, "no HTML version" if not html else "theorem not found"))
            continue
        url = f"{base}#{anchor}"
        text = path.read_text(encoding="utf-8")
        old = f"- paper: {pid}\n  reference: {reference}\n"
        if old not in text:
            missed.append((path.stem, pid, reference, "source not in the expected format"))
            continue
        if not dry:
            path.write_text(text.replace(old, f"{old}  url: {url}\n", 1), encoding="utf-8", newline="\n")
        linked.append((path.stem, pid, reference, url))

    for row in linked:
        print("linked ", " | ".join(row))
    for row in missed:
        print("missed ", " | ".join(row))
    print(f"{len(linked)} linked, {len(missed)} not linked{' (dry run)' if dry else ''}")


if __name__ == "__main__":
    main()
