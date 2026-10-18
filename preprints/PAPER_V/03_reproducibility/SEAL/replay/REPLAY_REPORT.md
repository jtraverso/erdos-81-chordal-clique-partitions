# Current SEAL execution and independent finite certificates

Date: 18 October 2026. **Status: PASS for the saved finite suites.** This report describes the Preprint 1.0 software package and its exact tested scope. The mathematical theorems and Lean source freeze remain separate from implementation validation.

## Executed models and data

All input host palettes are saved in `inputs/`. The BASE suite uses eighteen saved instances in four Python modes: standard cardinality, positive weighted objective, capacity-two cardinality, and potential-tracked cardinality. Weighted test inputs use weights in `{1,2,5,10}`; capacity-two inputs have capacity two at every host. JavaScript and C++ execute the standard, weighted and capacity-two modes on the same eighteen instances and export their actual selected families.

The v3 suite uses standard cardinality and capacity one. It includes the eighteen release instances, two explicit bipartite witnesses, and the following eighteen larger configurations saved explicitly in `inputs/`: rand `(24,60),(32,100),(40,140)`, bigrand `(24,40),(32,60),(40,80)`, and rr `(24,6),(32,8),(40,10)`, each with seeds one and two. Full generated palettes, outputs and rational dual vectors are saved; a configuration name or seed is not the only retained input. v3 rejects unsupported weighted/capacity settings rather than reporting a cardinality gap for a different objective.

`SOURCE_SNAPSHOT.json` fixes the four runtime sources and the supplied instance files. `INPUT_MANIFEST.json` binds all saved input files. The final Python capture ran after those runtime sources were frozen. C++ was compiled from its final source; the current reader accepts the saved indented JSON. `RUNS.json` and `PORT_RUNS.json` retain commands, durations and exit statuses. Every final command exited zero. No ILP optimum/timing benchmark was needed or run.

## Verified current results

| Check | Result |
|---|---:|
| Python BASE physical packings | 72: eighteen in each of four modes |
| Python v3 physical packings | 38: eighteen release, two witnesses, eighteen larger configurations |
| JavaScript physical packings | 54 |
| C++ physical packings | 54 |
| Complete rational cardinality duals | 38 |
| Object inequalities checked | 149,819 |
| Dual rows checked | 47,015 |
| Cardinality optima certified by equal lower/upper bounds | 12: six release, two witnesses, four larger configurations |
| Remaining positive certified intervals | 26 |
| Independent negative controls rejected | 7 |

The twelve remaining release intervals have gaps from one to three. The fourteen remaining larger-configuration intervals have gaps from one to forty. A positive interval is a bound on uncertainty; neither its lower endpoint nor a solver's numerical status is reported as the true optimum. `CURRENT_RESULTS.csv` contains the complete current per-instance table. Weighted and capacity-two BASE outputs have physical feasibility/objective checks, but no claimed optimum or approximation ratio from these tests.

The independent checker imports no implementation or solver. It reconstructs host containment, global pair uniqueness, per-host degree capacities, cardinality and the weighted objective from the input and selected pairs. It verifies these properties for all 218 Python/JavaScript/C++ outputs. It also checks the two physical states of a separate explicit N1 witness. The 54 objective coordinates from each port agree with Python on this suite; this finite agreement is not a universal equivalence theorem.

For each v3 certificate, the checker validates the semantics and nonnegative rational price of every pair, degree and odd-set row. It reconstructs every host-pair object and verifies coverage at least one. The exact rational sum of price times right-hand side gives the upper bound, and its floor gives the integral bound. Omitted valid matching inequalities may weaken that bound but do not invalidate the checked dual. No claim that the generated dual is always LP-optimal is required. Solver generation is separate from exact certificate replay.

The seven rejected corruptions are repeated pair, pair outside its host, false size, false weighted objective, zero dual undercoverage, false dual objective, and excessive host degree. Source and input hashes are checked before the replay.

## N1 operation and separate regression coverage

The current N1 operation is transactional: it releases a blocker, tests the relocation and target insertion, accepts a positive-value insertion, or restores the original state. On the selected BASE trajectories the recorded accepted N1 counts sum to 15 standard, 8 weighted, 2 capacity-two and 9 potential-tracked moves. These are accepted transitions in the returned trajectories, not the number of final blocks; multi-start trajectories that were not selected are not included. The potential-tracked mode uses one recorded scarcity trajectory.

The explicit two-host witness starts with one selected pair and ends with two, with one accepted N1 move. Both states are independently checked as physical packings. A separate finite exhaustive transaction regression, supplied in `control/N1_EXHAUSTIVE.json`, checks 685 feasible initial states and 27,708 operation trials on two stated host systems, capacities one/two and gains zero/one: 3,180 accepted insertions and 24,528 rejected trials with state restoration. That record names the same final Python source hash. It is additional finite regression evidence, not a universal proof. The implementation owner also supplies cross-language transaction tests under `current/tests/`.

## Reproduction

From the directory containing `current/` and `replay/`, check all saved outputs using only standard-library Python:

```sh
python replay/scripts/check_outputs.py --source-root current
```

Use ordinary Python without `-O` so assertions remain active. To regenerate the tested suites:

```sh
python replay/scripts/run_suite.py --source-root current
python replay/scripts/run_ports.py --source-root current
python replay/scripts/check_outputs.py --source-root current
```

Generation requires the documented Python/PuLP/CBC environment; the port runner requires Node and a C++17 compiler. Use `--cxx /path/to/g++` if compiler discovery does not find it. Each Python case has a 180-second process limit; these runs completed without timeouts. Timing records are descriptive and are not new speedup comparisons. Full exact duals, rather than a floating LP objective or an ILP status, justify the certified upper bounds.

This release account contains current results only. Private development comparisons and failed preparation attempts are kept outside the distribution. The current BASE variants implement insertion and N1; the separate unweighted `reference_v1` has explicit N1/N2 tests. Neither should be identified with a fully verified implementation of every mathematical branch. The v3 bipartite routine validates returned assignments, and its successful finite witnesses do not prove universal success in the local BKW range. No end-to-end Lean software verification or verified polynomial runtime is claimed here.
