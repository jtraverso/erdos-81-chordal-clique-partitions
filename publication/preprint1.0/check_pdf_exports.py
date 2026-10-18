"""Check the current PDF exports; visual inspection is recorded separately.

Requires PyMuPDF. Copyright 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import json
import re
import sys
import fitz

root = Path(__file__).resolve().parents[2]
index = json.loads((root / 'PUBLICATION_INDEX.json').read_text(encoding='utf-8'))
records = []
failures = []
for work in index['works']:
    for role, folder, stem in [
        ('main', '01_manuscript', work['main_stem']),
        ('companion', '05_formalization', work['companion_stem']),
    ]:
        for language in ('en', 'es'):
            path = root / work['path'] / folder / (stem + '_' + language + '.pdf')
            if not path.exists():
                failures.append(str(path.relative_to(root)) + ': missing PDF')
                continue
            with fitz.open(path) as doc:
                texts = [page.get_text() for page in doc]
                text = '\n'.join(texts)
                bad = re.findall(r'working\s+draft|borrador|draft remains subject|EDITORIAL_DRAFT|computational revision 2|ROOT_HASH|CLOSURE_HASH|ARCHIVE_HASH', text, re.I)
                private = re.findall(r'C:[/\\]+Users[/\\]+jtraverso|Camara de Comercio de Santiago|CCS_NOTEBOOK', text + json.dumps(doc.metadata), re.I)
                outside = []
                for number, page in enumerate(doc, 1):
                    for block in page.get_text('blocks'):
                        x0, y0, x1, y1 = block[:4]
                        if x0 < -1 or y0 < -1 or x1 > page.rect.width + 1 or y1 > page.rect.height + 1:
                            outside.append(number)
                record = {'path': path.relative_to(root).as_posix(),
                          'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                          'work': work['work'], 'role': role, 'language': language,
                          'pages': len(doc), 'preprint_1_0_on_first_page': bool(re.search(r'Preprint\s+1\.0', texts[0], re.I)),
                          'draft_or_unresolved_markers': bad, 'private_paths': private,
                          'text_outside_media_box_pages': sorted(set(outside))}
                records.append(record)
                if bad or private or outside or not record['preprint_1_0_on_first_page']:
                    failures.append(record['path'])
report = {'status': 'PASS' if len(records) == 16 and not failures else 'FAIL',
          'scope': 'Sixteen current PDF exports: text extraction, edition labels, unresolved markers, workstation paths, and media-box geometry. Does not replace visual inspection.',
          'documents': records, 'failures': failures}
(Path(__file__).parent / 'PDF_EXPORT_CHECK.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps({'status': report['status'], 'pdfs': len(records), 'pages': sum(x['pages'] for x in records), 'failures': failures}, indent=2))
sys.exit(report['status'] != 'PASS')
