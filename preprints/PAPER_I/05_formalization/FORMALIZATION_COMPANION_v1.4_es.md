# Paper I: formalización y reproducibilidad

**Juan Pablo Traverso Gianini**

Complemento de la edición editorial 1.4 · 19 October 2026

Este documento acompaña al artículo matemático. Conserva las declaraciones formales, las precisiones de alcance y la evidencia computacional que antes figuraban en el artículo. El congelado de fuentes y su verificación registrada no cambian. No se ejecutó Lean/Lake para esta edición. Los números históricos de secciones y tablas que siguen remiten al artículo anterior; se conservan como localizadores y no se renumeran como resultados nuevos de verificación. Las referencias originales [1], [2], etc. figuran al final.

[Frozen sources and historical evidence / Fuentes congeladas y evidencias históricas](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/05_formalization) · [Previous article / Artículo anterior](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/01_manuscript)

### Teorema 1.1

**Estado de la formalización.** El freeze Paper I Lean v1.2 usa Lean 4 / Mathlib v4.28.0 [6,7] y registra el Teorema 1.1 como `paperI_main_sharp`. La declaración `paperI_main` proporciona una forma compañera más débil con término aditivo \(n\). En estos nombres registrados, `sharp` se refiere al coeficiente cuadrático \(1/6\), no a la optimalidad del término aditivo. El gate de axiomas cubre el teorema principal, `PaperI.assembly_sharp`, `PaperI.Split.residual_duality`, la dualidad finita empaquetamiento–cobertura de la Proposición B.1 y las declaraciones de interfaz enumeradas en la Sección 10. Su huella registrada es `propext`, `Classical.choice` y `Quot.sound`, sin axiomas matemáticos propios del proyecto. La Sección 10 presenta el registro del freeze y del archivo.

## 10. Reproducibilidad y registro de la demostración

La demostración es analítica. Durante el desarrollo se usaron experimentos computacionales para buscar contraejemplos y detectar errores de transcripción, pero ningún cálculo es una premisa lógica del teorema. Por esa razón, el material de regresión computacional se mantiene fuera del artículo, en lugar de incluirse como un segundo apéndice.

El ledger de cálculos adjunto registra:

- cada identidad exacta;
- cada dirección de desigualdad;
- la contabilidad completa de pérdidas;
- la rama \(q=0\);
- los regímenes de órbitas;
- la conversión final a \(n\).

El autor reporta una auditoría adversarial interna asistida por IA del enunciado del teorema, la cota cuantitativa y el ensamblaje de la demostración. Este es un registro de validación, no una afirmación de revisión externa por pares.

### Estado de formalización en Lean

El snapshot en `PAPER_I/05_formalization/lean_v1.2_freeze` contiene las fuentes Lean y un build registrado exitoso de 8.034 jobs con Lean 4 / Mathlib v4.28.0 [6,7]. Contiene `paperI_main_sharp`, cuyo enunciado es `Phi ≤ n^2/6 + n/2`, junto con la declaración compañera más débil `paperI_main` y los resultados de interfaz enumerados más abajo. Su gate de axiomas también consulta `PaperI.assembly_sharp` y `PaperI.Split.residual_duality`. El Apéndice C registra la declaración principal. Posteriormente, el archivo exacto se reprodujo en un clean room externo con el mismo resultado de 8.034 jobs y la misma huella axiomática por teorema.

El informe de axiomas congelado registra únicamente los axiomas fundacionales estándar de Lean, `propext`, `Classical.choice` y `Quot.sound`, para el teorema principal y las declaraciones enumeradas; no registra ningún axioma matemático propio del proyecto. Se trata de fundamentos lógicos usados en todo Mathlib, no de supuestos matemáticos adicionales del artículo.

El artefacto de release también registra la dualidad finito-dimensional empaquetamiento-cobertura usada en Proposición B.1. En Lean aparece como `residual_duality`, una aplicación del teorema general `covering_packing_duality`. El artefacto registra este último teorema como derivado de un lema de Farkas finito y de la infraestructura de conos cerrados de Mathlib, en lugar de postularlo como un axioma externo. Schrijver [4, Capítulo 7] sigue siendo la referencia clásica para la demostración escrita.

El archivo de fuentes congelado es `PAPER_I_lean_v1.2_freeze.zip`, con SHA-256 `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`. Se almacena bajo `PAPER_I/05_formalization/lean_v1.2_freeze` y excluye los caches del proyecto y los objetos compilados. El target del build congelado incluye varios módulos `Contrib` destinados a un posible upstream; esa vía de contribución es un subproducto y no forma parte de los supuestos matemáticos de confianza del artículo. El informe de axiomas anterior controla la afirmación sobre dependencias lógicas. La reproducción externa en clean room corresponde exactamente a estos bytes del archivo; la revisión del manuscrito no modifica el artefacto formal.

---

## Apéndice C. Enunciado formalizado

El artefacto formal adjunto registra la siguiente declaración Lean 4 para el Teorema 1.1:

```lean
theorem paperI_main_sharp (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2

-- forma compañera más débil (término aditivo mayor):
theorem paperI_main (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ)
```

Aquí `Split` empaqueta los datos de un grafo split usados en la demostración: una clique de tamaño `p`, un tipo de vértices independientes y los vecindarios de esos vértices dentro de la clique. El campo `n` es el número total de vértices. La cantidad `Phi` se define como `|E| − 2·nu3star`, donde `nu3star` es el supremo de los valores factibles de empaquetamiento fraccional de triángulos. En otros artículos de la serie este déficit fraccional se escribe \(\Phi^*\), mientras que \(\Phi\), sin estrella, se reserva para el déficit integral \(|E(G)|-2\nu_3(G)\); el identificador Lean se conserva para coincidir con la declaración registrada. Con estas definiciones, `paperI_main_sharp` es exactamente

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+\frac{n}{2},
\]

la desigualdad enunciada en el Teorema 1.1 (declaración `paperI_main_sharp`). La declaración compañera `paperI_main` registra el término aditivo más débil \(n\).

El informe de build suministrado registra cero `sorry`. El informe de axiomas suministrado es:

```text
PaperI.Split.paperI_main_sharp depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.paperI_main         depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.assembly_sharp      depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.Split.residual_duality depends on axioms: [propext, Classical.choice, Quot.sound]
```

Estos son los tres axiomas fundacionales estándar de Lean y Mathlib. No se usa ningún axioma específico del proyecto.

**Tabla 2. Perímetro de la formalización congelada (freeze Lean v1.2).** El snapshot congelado de Lean 4 / Mathlib v4.28.0 registra el núcleo demostrado usando únicamente los axiomas fundacionales estándar de Lean y ningún axioma matemático propio del proyecto. Una compilación externa en clean room y una comprobación de axiomas por teorema reprodujeron el archivo exacto.

| Nodo | Enunciado | Huella axiomática |
|---|---|---|
| `paperI_main_sharp` (Teorema 1.1) | \(\lvert E(G)\rvert-2\nu_3^*(G)\le n^2/6+n/2\) | `propext`, `Classical.choice`, `Quot.sound` |
| `paperI_main` (cota compañera más débil) | \(\lvert E(G)\rvert-2\nu_3^*(G)\le n^2/6+n\) | `propext`, `Classical.choice`, `Quot.sound` |
| `lpVal_concave`, `lpVal_ge_min` (interfaz de §5) | concavidad abstracta / cota inferior por perfiles puros | `propext`, `Classical.choice`, `Quot.sound` |
| `lpVal_lipschitz` (interfaz de §5) | estabilidad paramétrica del valor fraccional | `propext`, `Classical.choice`, `Quot.sound` |
| `residual_duality` (Prop. B.1) | dualidad finita empaquetamiento–cobertura | `propext`, `Classical.choice`, `Quot.sound` |

### Proposición B.1

**Nota de formalización.** El freeze v1.2 registra la Proposición B.1 como la declaración Lean `PaperI.Split.residual_duality`, una instancia del teorema general de dualidad fuerte finita `covering_packing_duality`. El artefacto registra este último como probado a partir de un lema de Farkas finito, usando el carácter cerrado de un cono convexo finitamente generado y el teorema de separación por hiperplanos para conos convexos cerrados. Por tanto, la dualidad usada aquí se deriva dentro del desarrollo formal y no se postula como un axioma específico del proyecto. Schrijver sigue siendo la referencia clásica para el argumento escrito. Las fuentes correspondientes, el log de build y el informe de axiomas se entregan en `PAPER_I/05_formalization/lean_v1.2_freeze`.

### 1. Introducción

**Notación de la serie.** En las comparaciones entre artículos, el déficit fraccional de Paper I se escribe \(\Phi^*(G)=|E(G)|-2\nu_3^*(G)\). Paper II denota la misma cantidad por \(\Phi_\tau(G)=|E(G)|-2\tau_3^*(G)\), mientras que Paper III reserva \(\Phi(G)\), sin estrella, para el déficit integral \(|E(G)|-2\nu_3(G)\). El identificador Lean `Phi` del artefacto de Paper I se conserva por trazabilidad.

### Observación (concavidad sobre un politopo fijo)

La reducción que acabamos de usar es un caso de un hecho puramente convexo-analítico, que formulamos aquí de manera abstracta. Fijemos un politopo factible que no dependa del perfil y una función objetivo que dependa afínmente de la masa del perfil \(\mu=(\mu_S)\). Como el valor óptimo de un programa lineal sobre un politopo fijo es cóncavo respecto de su vector objetivo, el valor en un perfil mixto domina la combinación convexa correspondiente de los valores de los perfiles puros y, por tanto, también su mínimo:
\[
M_b(\kappa_\mu)\ \ge\ \sum_S \tfrac{\mu_S}{q}\,M_b(\kappa^{S,q})\ \ge\ \min_S M_b(\kappa^{S,q}).
\]
Esto se registra en el desarrollo formal como `lpVal_concave` y `lpVal_ge_min`. Una estimación complementaria, `lpVal_lipschitz`, acota la variación del valor fraccional cuando se perturban el baseline o la distribución de perfiles. Está pensada para variantes robustas y casi split. Ambas se formulan para un politopo factible fijo con una función objetivo que varía afínmente; ninguna requiere simetría, que solo interviene después, sobre un único perfil puro, en la Sección 6.


## Referencias

[1] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[2] G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30, copia alojada por uno de los autores: https://ordman.net/MathResearch/CEOClique_Parts.pdf, consultada el 21 de agosto de 2026.

[3] T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, consultado el 21 de agosto de 2026.

[4] A. Schrijver, *Theory of Linear and Integer Programming*, Wiley-Interscience Series in Discrete Mathematics and Optimization, John Wiley & Sons, Chichester, 1986.

[5] M. S. Cavers, *Clique Partitions and Coverings of Graphs*, M.Math. essay, University of Waterloo, 2005.

[6] L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language,” in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science **12699**, Springer, 2021, pp. 625–635, https://doi.org/10.1007/978-3-030-79876-5_37.

[7] The mathlib Community, “The Lean Mathematical Library,” in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367–381, https://doi.org/10.1145/3372885.3373824.

