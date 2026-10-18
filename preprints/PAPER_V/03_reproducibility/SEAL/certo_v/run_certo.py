"""Scoped scalar obligations from Paper V; not a substitute for graph constructions.
Author: Juan Pablo Traverso Gianini.
"""
from pathlib import Path
import hashlib
import importlib.metadata
import json
import subprocess
import shutil
import sys

OUT = Path(__file__).resolve().parent
OUT.mkdir(parents=True, exist_ok=True)
CLI = shutil.which('certo') or str(Path(sys.executable).parent/'Scripts/certo.exe')
CASES = {
    'two_error_transfer': ('W,L,U,g,r = Reals("W L U g r")',
       [('dual_upper','W <= U'),('realization_lower','L-r <= g'),('feasible_gain','g <= W')],
       'And(0 <= W-g, W-g <= U-L+r)'),
    'integer_dual_stop': ('nu,R = Ints("nu R"); U = Real("U")',
       [('feasible','R <= nu'),('dual','nu <= U'),('stop','U < R+1')], 'nu == R'),
    'composed_realization_errors': ('W,L,U,g,h,r,t = Reals("W L U g h r t")',
       [('dual','W <= U'),('first','g >= L-r'),('second','h >= g-t'),('feasible','h <= W')],
       'And(W-h >= 0,W-h <= U-L+r+t)'),
    'improving_repairs_budget': ('initial,final,steps,cover = Ints("initial final steps cover")',
       [('start','initial >= 0'),('improvement','final >= initial+steps'),('capacity','final <= cover')],
       'steps <= cover-initial'),
    'gap_residual_and_resource_defect': ('relax,nu,cover,epsilon = Reals("relax nu cover epsilon")',
       [('feasible_pairs','nu <= cover'),('resource_excess','relax-cover <= epsilon'),
        ('relaxation','nu <= relax')],
       'And(0 <= relax-nu, relax-nu <= cover-nu+epsilon)'),
    'residual_does_not_bound_relaxation_gap': ('nu,relax,cover = Reals("nu relax cover")',
       [('all_scheduled','nu == cover'),('upper_relaxation','relax >= nu'),('positive','nu >= 0')],
       'relax == nu'),
}


def call(args, log):
    result = subprocess.run([CLI, *args, '--json', '--brief'], cwd=OUT, capture_output=True,
                            text=True, encoding='utf-8', timeout=70)
    (OUT/log).write_text(result.stdout+'\nSTDERR\n'+result.stderr, encoding='utf-8')
    return result.returncode, json.loads(result.stdout)


records = []
for name, (variables, hypotheses, claim) in CASES.items():
    source = ('# Author: Juan Pablo Traverso Gianini\nfrom certo import Spec\nfrom z3 import Reals, Real, Ints, And\n\ndef spec():\n'
              f'    {variables}\n    s = Spec()\n')
    source += ''.join(f'    s.assume({label!r}, {condition})\n' for label,condition in hypotheses)
    source += f'    s.claim({claim})\n    return s\n'
    spec = OUT/f'{name}.py'
    spec.write_text(source, encoding='utf-8')
    cert = f'{name}.certificate.json'
    code, proved = call(['prove', spec.name, '--cert', cert, '--deadline', '60'], name+'.prove.log')
    counterexample = name == 'residual_does_not_bound_relaxation_gap'
    if counterexample:
        assert proved['verdict'] in ('disproved','refuted'), proved
    else:
        assert code == 0 and proved['verdict'] == 'proved', proved
    code2, replay = call(['verify', cert, '--spec', spec.name, '--obligation', spec.name], name+'.verify.log')
    assert code2 == 0 and replay['ok'] is True and not replay.get('assumed') and not replay.get('partial'), replay
    records.append({'name': name, 'spec_sha256': hashlib.sha256(spec.read_bytes()).hexdigest(),
                    'prove': proved, 'verify': replay, 'exit_prove': code, 'exit_verify': code2,
                    'certificate_sha256': hashlib.sha256((OUT/cert).read_bytes()).hexdigest()})
wrong = OUT/'wrong_obligation.py'
wrong.write_text((OUT/'two_error_transfer.py').read_text().replace('W-g <= U-L+r','W-g <= U-L+r-1'), encoding='utf-8')
code, mismatch = call(['verify', 'two_error_transfer.certificate.json', '--spec', wrong.name,
                       '--obligation', wrong.name], 'negative_wrong_obligation.log')
assert code != 0, mismatch
code, semantic_mismatch = call(['verify', 'two_error_transfer.certificate.json',
                                '--obligation', wrong.name], 'negative_changed_target.log')
assert code != 0 and semantic_mismatch.get('ok') is False, semantic_mismatch
(OUT/'RESULTS.json').write_text(json.dumps({'status': 'PASS_SCOPED', 'certo_version': importlib.metadata.version('certo-math'),
    'records': records, 'wrong_obligation_rejected': mismatch,
    'changed_target_rejected_without_source_hash_check': semantic_mismatch,
    'scope': 'SMT scalar implications and one explicit counterexample; no proof of a combinatorial existence theorem. Solver-dependent certificates are labelled in each record.'}, indent=2)+'\n', encoding='utf-8')
print('PASS', len(records))
