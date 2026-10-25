#!/usr/bin/env python3
"""Shrink the doc-gen4 output to the Cutfast pages, for GitHub Pages.

doc-gen4 documents every imported module (1.3 GB, mostly Mathlib), over the 1 GB limit of
GitHub Pages. This keeps the Cutfast module pages, the shared assets and the search data, and
deletes the pages of the dependencies. Their links (from Cutfast pages, the navigation bar and
search results) then hit `404.html`, which is made to redirect them to the same page of the
upstream documentation.

Usage: python3 scripts/prune-docs.py docbuild/.lake/build/doc
"""
import pathlib
import shutil
import sys

UPSTREAM = "https://leanprover-community.github.io/mathlib4_docs/"
KEEP = {"Cutfast", "declarations", "find"}

REDIRECT = """<script>
(function () {
  var m = location.pathname.match(/\\/((?:%s)(?:\\/|\\.html).*)$/);
  if (m) location.replace("%s" + m[1] + location.search + location.hash);
})();
</script>"""


def main() -> None:
    doc = pathlib.Path(sys.argv[1])
    if not (doc / "Cutfast.html").is_file() or not (doc / "404.html").is_file():
        sys.exit(f"{doc} is not a doc-gen4 output")
    removed = sorted(p.name for p in doc.iterdir() if p.is_dir() and p.name not in KEEP)
    for name in removed:
        shutil.rmtree(doc / name)
        (doc / f"{name}.html").unlink(missing_ok=True)
    page = doc / "404.html"
    script = REDIRECT % ("|".join(removed), UPSTREAM)
    page.write_text(page.read_text(encoding="utf-8").replace("<head>", "<head>" + script, 1),
                    encoding="utf-8")
    print(f"removed the pages of {', '.join(removed)}")


if __name__ == "__main__":
    main()
