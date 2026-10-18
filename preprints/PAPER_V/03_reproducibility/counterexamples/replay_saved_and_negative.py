# Copyright (c) 2026 Juan Pablo Traverso Gianini.
# Released under Apache License 2.0; see the series software LICENSE.
"""Replay the saved BK certificate and an altered-certificate negative control."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile

if not __debug__:
    raise RuntimeError('Assertions must remain enabled; do not use Python -O.')
root=Path(__file__).resolve().parent
source=root/'bk_completion_certificates.py'
certificate=root/'BK_ANCILLARY_CERTIFICATES.json'
cmd=[sys.executable,'-X','utf8',source.name,'--verify-only']
good=subprocess.run(cmd,cwd=root,capture_output=True,text=True,encoding='utf-8')
assert good.returncode==0,good.stderr
(root/'VERIFY_SAVED.log').write_text(good.stdout,encoding='utf-8')
with tempfile.TemporaryDirectory(prefix='bk_saved_negative_')as directory:
    temp=Path(directory);shutil.copyfile(source,temp/source.name)
    data=json.loads(certificate.read_text(encoding='utf-8'))
    data['exact_dual'][0]['price']='0'
    (temp/certificate.name).write_text(json.dumps(data),encoding='utf-8')
    bad=subprocess.run(cmd,cwd=temp,capture_output=True,text=True,encoding='utf-8')
    assert bad.returncode!=0 and 'AssertionError' in bad.stderr
(root/'NEGATIVE_CONTROL.log').write_text('Altered saved dual price was rejected.\nexit_code='+str(bad.returncode)+'\nAssertionError observed=True\n',encoding='utf-8')
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record={'status':'PASS','python_version':sys.version.split()[0],
        'source_sha256':digest(source),'certificate_sha256':digest(certificate),
        'replay_script_sha256':digest(Path(__file__)),
        'verify_command':['python',source.name,'--verify-only'],
        'verify_exit_code':good.returncode,'negative_control_exit_code':bad.returncode,
        'negative_control':'Altered first dual price rejected by the unchanged verifier.',
        'scope':'Exact finite unit-capacity BK instance. The rational dual of value 19/2 gives the integral upper bound 9. All 70 feasible nine-element optimal families and beta=2 are recomputed. This is not a universal proof or an end-to-end Lean verification of Python.'}
(root/'VALIDATION.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('PASS: saved certificate; altered certificate rejected')
