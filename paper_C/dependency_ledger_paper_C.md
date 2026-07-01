# Dependency Discipline

## Linear dependency rule

The proof series is ordered linearly:

\[
\text{Paper A} \rightarrow \text{Paper B} \rightarrow \text{Paper C} \rightarrow \text{Paper D}.
\]

The citation discipline is:

| Paper | May cite | Must not cite |
|---|---|---|
| Paper A | none, except standard external references | Paper B, C, D |
| Paper B | Paper A and standard external references | Paper C, D |
| Paper C | Paper A, Paper B, and standard external references | Paper D |
| Paper D | Paper A, Paper B, Paper C, and standard external references | none in the series |

## Gates are historical notes

The gates are research logs. They are not part of the formal dependency chain.

A paper should not rely on a gate unless the gate-derived content is restated in one of:

1. the paper itself;
2. this roadmap folder;
3. a calculation ledger;
4. a reproducible certificate package.

## No backward dependencies

A local result in Paper B cannot depend on a global assembly result in Paper C.

A fractional theorem in Paper C cannot depend on the integral rounding in Paper D.

This prevents circularity.

## Machine-checkable components

Machine-checkable components are allowed, but they must be:

1. finite;
2. exact, preferably rational;
3. reproducible from repository files;
4. documented in a README;
5. explicitly separated from the structural proof.

The current example is the boundary-export \(L_4\) certificate family.

## Certificate citation rule

The paper may cite a certificate only after:

1. the structural reduction has isolated the finite local residue;
2. the certificate scope is stated exactly;
3. the certificate verifier is included in the repository;
4. the expected verifier output is recorded.

The \(L_4\) certificate should never be cited as an unrestricted span-four window-sweep theorem.
