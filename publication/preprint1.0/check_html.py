"""Check publication HTML structure and local links, without browser rendering.

Copyright 2026 Juan Pablo Traverso Gianini
SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
import hashlib
import json
import sys

root = Path(__file__).resolve().parents[2]
works = json.loads((root / 'PUBLICATION_INDEX.json').read_text())['works']
records = []
class Page(HTMLParser):
    def __init__(self):
        super().__init__(); self.links = []; self.tags = []
    def handle_starttag(self, tag, attrs):
        self.tags.append(tag)
        attrs = dict(attrs)
        if tag in ('a', 'link') and attrs.get('href'): self.links.append(attrs['href'])
        if tag in ('img', 'script') and attrs.get('src'): self.links.append(attrs['src'])

for path in [root / 'index.html'] + [root / w['path'] / 'index.html' for w in works]:
    text = path.read_text(encoding='utf-8'); page = Page(); page.feed(text)
    broken = []
    for link in page.links:
        url = urlsplit(link)
        if url.scheme or url.netloc or not url.path: continue
        if not (path.parent / unquote(url.path)).exists(): broken.append(link)
    structural = all(tag in page.tags for tag in ('html', 'head', 'title', 'body'))
    records.append({'path':path.relative_to(root).as_posix(),
                    'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                    'structure_present':structural, 'broken_local_links':broken})
passed = all(r['structure_present'] and not r['broken_local_links'] for r in records)
report = {'status':'PASS_SOURCE_AND_LINKS' if passed else 'FAIL',
          'scope':'HTML source structure and local navigation. Browser visual capture was blocked by tool policy and is not claimed.',
          'pages':records}
(Path(__file__).parent / 'HTML_CHECK.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2)); sys.exit(not passed)
