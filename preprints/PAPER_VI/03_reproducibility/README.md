# Paper VI Preprint 1.0: finite regression evidence

These are finite checks, separate from the universal written and Lean proofs. The scripts produce and independently verify explicit graph partitions. No finite sample or census is a premise of a universal theorem.

## New cases

- 18 local certificates for A–C: exact balanced and general thresholds, all allowed exterior sizes, three simultaneous edit classes, concentrated degree-two stars, an exterior cycle and mixed prescriptions at the 63h threshold.
- 15 one-exceptional-vertex certificates with p = 2, q = 5, all a = 0,1,2 and b = 0,1,2,3,4. The independent verifier checks signed partition duals, triangle-cover duals and attained integral witnesses.
- One three-state recourse certificate with two exterior edges: one protected lifting, one changed lifting, 1938 retained compatible terminal triangles, 24 lost blocks, symmetric difference 48 and terminal distance 6. The independent replay verifies complete-join and bounded-load membership of every state.

## Reproduction

From this directory, using Python 3 with its standard library:

```text
python generate_v06.py
python verify_v06.py
python recourse_v06.py
python verify_recourse_v06.py
```

`historical_generator.py` is copied from the earlier construction dossier. It supplies a heuristic for finite examples, not an implementation of the universal list-edge-coloring proof. `verify_v06.py` and `verify_recourse_v06.py` do not import generator code.

With Certo installed, run:

```text
python run_certo_v06.py
python run_certo_recourse_v06.py
```

Six generated exact-cover certificates are verified against their exact specification files. The certificates record the installed Certo version and whether the check was solver-free. The Certo objective here is validation of the supplied edge partition; its output is not presented as a standalone proof of global optimality. The independent dual witnesses supply the finite optimality certificate.

Three further Certo certificates validate exact edge coverage in each supplied recourse state. The independent replay separately verifies path distance, protection, lifting-class membership and the finite optimum count.

Three corruptions fail the independent verifier: missing coverage, repeated coverage and a wrong prescription. A changed specification identity is separately refused by Certo's provenance check; this is not a solver rejection or a mathematical counterexample. Two further recourse controls reject understated distance and load bounds.

Certo binds a certificate to the precise specification identity and hash. Running the generator in a relocated copy creates new tool certificates with the new local provenance; it does not silently alter the historical certificate identities.

## Public provenance

The nine Certo certificates were regenerated and verified for this public release in a neutral build directory. Supplied graph partitions and their independent dual certificates are preserved. Workstation paths in transcript copies are replaced by portable labels; the relocation record includes original and public-copy SHA-256 values. No certificate was edited to change its provenance. Development archives remain outside this public package.

These internal AI-assisted checks are distinct from human refereeing. The same independent checks were replayed after publication packaging. See ../02_validation/PUBLICATION_1_0/ for the evidence.
