# SEAL — código, experimentos y certificados / code, experiments and certificates

Autor / Author: Juan Pablo Traverso Gianini. Preprint 1.0, 18 October 2026.

Este paquete público contiene la implementación vigente y los resultados comprobados de sus experimentos. Las pruebas universales del artículo y el freeze Lean se documentan por separado en el complemento formal. / This public package contains the current implementation and checked experimental results. Universal theorems and the Lean freeze are documented separately in the formal companion.

## Implementaciones / Implementations

- `current/python/seal.py`, `current/js/seal.js`, `current/cpp/seal.cpp`: inserción y N1 con capacidades y pesos. N1 acepta una inserción de ganancia positiva o restituye el estado inicial. / Insertion and N1 with capacities and weights. N1 accepts a positive-gain insertion or restores the initial state.
- `current/python/seal_v3.py`: generación de certificados duales para cardinalidad con capacidad uno; exporta todas sus filas racionales. / Cardinality certificate generation with capacity one; exports all rational dual rows.
- `reference_v1/`: referencia separada de cardinalidad y capacidad uno con movimientos N1/N2 y verificador independiente. / Separate unit-capacity cardinality reference with N1/N2 moves and an independent checker.
- `certo_v/`: certificados algebraicos complementarios; su alcance está indicado en cada evidencia. / Supplementary algebraic certificates with their stated scope.

## Resultados / Results

Se comprobaron 218 packings físicos: 110 Python, 54 JavaScript y 54 C++. Los 38 certificados racionales comprueban 149 819 desigualdades de objetos y 47 015 filas duales. Doce casos certifican óptimo por igualdad de cotas; los otros 26 conservan intervalos certificados. Los ensayos ponderados y de capacidad dos verifican factibilidad y valor, sin afirmar optimalidad. / The independent checker validated 218 physical packings: 110 Python, 54 JavaScript and 54 C++. The 38 rational certificates check 149,819 object inequalities and 47,015 dual rows. Twelve cases certify optimality by matching bounds; the remaining 26 retain certified intervals. Weighted and capacity-two tests check feasibility and objective value without an optimality claim.

La tabla completa y el alcance están en [CURRENT_RESULTS.csv](replay/CURRENT_RESULTS.csv) y [REPLAY_REPORT.md](replay/REPLAY_REPORT.md). Se guardan entradas completas, salidas, certificados, comandos y hashes. / Full results and scope are in the linked table and report. Complete inputs, outputs, certificates, commands and hashes are retained.

Las regresiones incluyen nueve casos transaccionales en los tres lenguajes y 27 708 operaciones sobre 685 estados pequeños en Python, con 3 180 inserciones aceptadas y 24 528 rechazos con restitución. Son comprobaciones finitas, no verificación universal del software. / Regressions include nine transactional cases in all three languages and 27,708 Python operations over 685 small states, with 3,180 accepted insertions and 24,528 rejected operations with restoration. These are finite checks, not universal software verification.

## Reproducir / Reproduce

Desde esta carpeta, con Python sin `-O` / From this directory, using Python without `-O`:

```sh
python replay/scripts/check_outputs.py --source-root current
python control/check_n1_exhaustive.py current
python reference_v1/check_certificate.py
```

El primer y tercer comando comprueban resultados guardados sin solver; el segundo vuelve a probar las operaciones sobre estados pequeños. / The first and third commands check saved results without a solver; the second reruns the small-state operation tests.

Para regenerar / To regenerate:

```sh
python replay/scripts/run_suite.py --source-root current
python replay/scripts/run_ports.py --source-root current
python current/tests/run_regressions.py
```

La generación usa Python 3.12, PuLP 3.3.2 con CBC 2.10.3, Node 24 y un compilador C++17. El informe conserva el entorno y los límites de ejecución. Los algoritmos heurísticos no garantizan óptimo en todas las entradas, y las comprobaciones finitas no prueban equivalencia universal entre puertos. / Generation uses Python 3.12, PuLP 3.3.2 with CBC 2.10.3, Node 24 and a C++17 compiler. The report records environment and execution limits. The heuristics do not guarantee optimality on every input, and finite comparisons do not prove universal equivalence between ports.
