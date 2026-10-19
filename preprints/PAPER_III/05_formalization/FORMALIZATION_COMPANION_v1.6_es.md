# Paper III: formalización y reproducibilidad

**Juan Pablo Traverso Gianini**

Complemento de la edición editorial 1.6 · 19 October 2026

Este documento acompaña al artículo matemático. Conserva las declaraciones formales, las precisiones de alcance y la evidencia computacional que antes figuraban en el artículo. El congelado de fuentes y su verificación registrada no cambian. No se ejecutó Lean/Lake para esta edición. Los números históricos de secciones y tablas que siguen remiten al artículo anterior; se conservan como localizadores y no se renumeran como resultados nuevos de verificación. Las referencias originales [1], [2], etc. figuran al final.

[Frozen sources and historical evidence / Fuentes congeladas y evidencias históricas](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_III/05_formalization) · [Previous article / Artículo anterior](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_III/01_manuscript)

## 11.6 Perímetro de verificación formal y estado actual

La discusión de la formalización se concentra en esta sección y en el registro de release de la Sección 13. El snapshot formal actual separa el ensamblaje final incondicional de sus interfaces downstream. La raíz pública agregada `PaperIII` importa tanto `PaperIII.Theorem_1_1_Final` como `PaperIII.PublicAPI`. El módulo final descarga las dos interfaces usadas por el artículo y exporta el Teorema 1.1 y el Corolario 1.2. `PaperIII.CanonicalTrianglePacking` fija `PaperIII.nu3` y `PaperIII.nu3Star` como cantidades orientadas al manuscrito y demuestra su igualdad con las implementaciones mediante hipergrafos de aristas utilizadas por AX1; también demuestra `PaperIII.tau3Star = PaperIII.nu3Star` e identifica la interfaz AX1 del lado de coberturas con el enunciado del lado de empaquetamientos de la Sección 2. `PaperIII.PaperImprovements` contiene los certificados orientados al artículo; `PaperIII.PublicAPI`, `PaperIII.OfPartition` y `PaperIII.Obstructions` exponen las interfaces downstream. El gate canónico dirigido informa la siguiente huella de axiomas para estas superficies:

```text
[propext, Classical.choice, Quot.sound]
```

El ensamblaje final usa puentes explícitos hacia las formalizaciones de Haxell--Rödl/Yuster y de descomposición densa. Los teoremas asintóticos citados se mantienen en el manuscrito por su procedencia matemática. El build registrado del lado del autor para la raíz pública completó 8.455 jobs con exit code 0; el build posterior de las raíces de consulta completó 8.444 jobs con exit code 0. Ese proceso del autor se reanudó después del reinicio de una aplicación. Por separado, la auditoría externa realizó una reproducción ininterrumpida desde la ausencia del directorio de build del proyecto: la raíz pública completó 8.455 jobs, las raíces de consulta completaron 8.444 jobs y los ocho archivos de consulta de axiomas terminaron correctamente. El archivo formal inmutable está sellado, y los gates Lean internos y externos pasan dentro del alcance declarado en la Sección 13.

El Apéndice E ofrece una selección curada de certificados reutilizables y de nivel paper. El inventario completo al nivel de implementación permanece en la fuente formal, en lugar de duplicarse en el manuscrito.

**Tabla 2. Superficies de formalización.** Los estados de esta tabla son registros del freeze local sellado; no sustituyen la reproducción independiente.

| Superficie | Propósito | Estado local actual |
|---|---|---|
| `PaperIII` | raíz agregada/de compatibilidad | el build de la raíz pública completó 8.455 jobs; exit 0; importa el teorema final y la API pública |
| `PaperIII.MainNibble` | ensamblaje del teorema y los corolarios mediante interfaces AX1/AX2 explícitas | compilada en la clausura registrada |
| `PaperIII.Theorem_1_1_Final` | descarga incondicional de AX1/AX2 y teorema final | compilada; la huella del teorema final es exclusivamente fundacional |
| `PaperIII.CanonicalTrianglePacking` | puentes canónicos para `nu3`, `nu3Star`, `tau3Star` y el enunciado AX1 | compilada; se registraron los puentes exactos del target |
| `PaperIII.CanonicalTrianglePackingGate` | gate de enunciados y axiomas para las interfaces canónicas | exit 0; huellas exclusivamente fundacionales registradas |
| `PaperIII.PaperImprovements` y `PaperIII.PaperImprovementsGate` | corolarios orientados al paper y certificados auxiliares seleccionados | compilados en la corrida consolidada de gates |
| `PaperIII.PublicAPI`, `PaperIII.OfPartition`, `PaperIII.Obstructions` | API downstream, transporte de partición split y certificados de obstrucción | compilados en la clausura registrada |
| `FREEZE_REPORT.md` y `ESCAPE_HATCH_ASSESSMENT.md` | evaluación inmutable del build, los axiomas y los tokens crudos | generados e incluidos en el archivo formal sellado |

Al nivel de `SimpleGraph`, `Theorem_1_1_of_splitPartition_uncond` acepta un grafo finito provisto de una partición clique/independiente. La construcción `SplitGraph.ofPartition` se conecta con el grafo original mediante `ofPartitionIso`; el número de vértices, el número de aristas, \(\nu_3\) y \(\Phi\) se transportan a través de la invariancia por isomorfismos de grafos, incluida `nu3_congr_of_iso`. Otras formas del teorema especializadas por tipos permanecen en `PaperIII.PublicAPI` para uso downstream, pero no son resultados matemáticos del artículo y no se catalogan aquí.

La compilación dirigida del módulo canónico, los builds de las raíces pública y de consulta, los ocho archivos compatibles de consulta de axiomas, la evaluación de escape hatches, los manifiestos inmutables de fuentes y la auditoría interna pasan sus controles del lado del autor. La auditoría externa reprodujo independientemente las raíces pública y de consulta y verificó las superficies de axiomas designadas contra los mismos bytes congelados.

Ningún cálculo ni script de regresión es premisa de la demostración. Las comprobaciones de aritmética exacta y programación entera siguen siendo auditorías suplementarias. La revisión adversarial completada y la evaluación de arte previo acotada por su corpus no sustituyen una revisión humana por pares ni una determinación especializada de prioridad; el etiquetado público es una operación de release al nivel del repositorio.

## 11.7 Componentes reutilizables de la formalización

La formalización también produjo una biblioteca independiente `Contrib.*`, cuyos módulos importan únicamente Mathlib. Cuatro grupos resultan especialmente pertinentes más allá de este artículo:

- dualidad fuerte finita para LP de empaquetamiento/cobertura mediante un argumento de Farkas cónico (`Contrib.LPStrongDuality`);
- desigualdades de concentración sensibles a la varianza y colas de martingalas (`Contrib.BennettBernstein`, `Contrib.HoeffdingUpper`, `Contrib.ConditionalHoeffding` y `Contrib.FreedmanBernstein`);
- resultados de tipo Dirac para hamiltonicidad y matchings (`Contrib.DiracHamiltonian` y `Contrib.SpreadMatchingDirac`);
- componentes finitos de flujo máximo/corte mínimo y de teoría de diseños (`Contrib.MaxFlowMinCut` y `Contrib.FanoSTS`).

Estos módulos son subproductos reutilizables de la formalización, no premisas del Teorema 1.1. Se reservan para una revisión separada y una posible contribución upstream. El presente manuscrito no afirma que sus APIs o sus enunciados individuales sean nuevos respecto de la biblioteca Mathlib vigente; esa comparación exige una revisión separada de literatura y de la API orientada a upstream. El Apéndice E.6 registra solo los componentes más cercanos a la demostración matemática.

---

## 13. Reproducibilidad

La fuente matemática es este manuscrito. Las superficies formales orientadas al manuscrito son `PaperIII.Theorem_1_1_Final`, `PaperIII.CanonicalTrianglePacking`, `PaperIII.PublicAPI`, `PaperIII.OfPartition` y `PaperIII.Obstructions`. `PaperIII.PaperImprovementsGate` es el gate de subproductos, y `PaperIII.CanonicalTrianglePackingGate` comprueba la correspondencia exacta entre los parámetros canónicos de empaquetamiento y el modelo Nibble/Yuster usado para descargar AX1.

El desarrollo formal está sellado como `PAPER_III_lean_v1.4_freeze.zip`, con SHA-256 `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`. Contiene 704 archivos fuente Lean y los tres archivos fijados de Lake/toolchain enumerados en el manifiesto de 707 entradas. La verificación registrada usa Lean 4.28.0 y Mathlib v4.28.0 en el commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

El registro local de verificación disponible se resume a continuación.

**Tabla 3. Registro local sellado de verificación.**

| Comprobación | Log o comando | Resultado actual |
|---|---|---|
| build de la raíz pública agregada | `gate_logs/run_2026-08-22_CCS_NOTEBOOK456_resumed/logs/02_build_public_root_clean.log` | exit 0; 8.455 jobs completados; proceso de origen limpio reanudado después del reinicio de una aplicación |
| completación de las raíces de consulta | `gate_logs/run_2026-08-22_CCS_NOTEBOOK456_resumed/logs/03_build_query_roots_incremental.log` | exit 0; 8.444 jobs completados |
| gate canónico de enunciados y axiomas | `PaperIII.CanonicalTrianglePackingGate` | exit 0; comprobados los puentes integrales y fraccionales del target |
| registro completo de axiomas por teorema | ocho archivos `FreezeAxioms*.lean` | exit 0; solo `propext`, `Classical.choice` y `Quot.sound` |
| regresión cuantitativa del cierre Lean | `FreezeAxiomsAuditClosure.lean` y `FreezeAxiomsAX1Closure.lean` | todas las superficies nombradas están presentes con huellas exclusivamente fundacionales |
| evaluación de escape hatches | escaneo de tokens crudos y controles enfocados de build/huellas | sin warning activo de `sorry`, sin `native_decide` activo y sin axioma de proyecto en una superficie canónica |
| sello inmutable | manifiestos de fuentes/paquete, ZIP y sidecar SHA-256 | 707 entradas fuente; hash del archivo verificado |

La verificación registrada usó un único snapshot de fuentes sin cambios. Su secuencia de build fue

```text
lake build PaperIII
lake build BKLO.MainDenseUnconditional Nibble.AX1Closed PaperIII.CanonicalTrianglePacking PaperIII.Obstructions PaperIII.PaperImprovementsGate PaperIII.PublicAPI PaperIII.Theorem_1_1_Final
#print axioms PaperIII.Theorem_1_1
#print axioms PaperIII.AX1_holds
#print axioms PaperIII.AX2_holds
```

El proyecto del lado del autor comenzó sin directorio `.lake` ni objetos compilados del proyecto. La aplicación de escritorio se reinició durante el primer proceso de la raíz pública; el proyecto, sin cambios, se reanudó entonces de manera incremental y terminó correctamente. Por ello, el freeze inmutable registra `PASS_CLEAN_ORIGIN_RESUMED`, no una única invocación ininterrumpida del autor. Conserva esa declaración, la salida verbatim, los identificadores de componentes, el manifiesto de fuentes, el manifiesto del archivo y los inventarios SHA-256. La auditoría externa aportó después una reproducción ininterrumpida desde la ausencia del directorio de build del proyecto, con las revisiones fijadas de las dependencias: 8.455 jobs de la raíz pública y 8.444 jobs de las raíces de consulta terminaron con exit code 0, y pasaron los ocho archivos de consulta de axiomas. Esos controles al nivel de declaraciones establecen conformidad del build y huellas de axiomas; no reemplazan una rederivación matemática independiente.

Dos módulos legacy archivados, `Ax2/PartB/Axioms.lean` y `Ax2/PartA/Wlog.lean`, contienen declaraciones de axiomas locales del proyecto. Ningún archivo fuente importa esos módulos y ninguna de esas declaraciones aparece en la huella de dependencias de una superficie canónica de release. Por tanto, el claim formal preciso es al nivel de declaraciones: el teorema canónico y las interfaces de release no tienen axiomas matemáticos locales del proyecto; no se afirma que el árbol histórico completo carezca del token `axiom`.

La demostración misma permanece en el manuscrito. Los scripts de regresión y las auditorías computacionales no son hipótesis, reducciones ni pasos de la demostración.

El paquete del repositorio canónico contiene la fuente Lean completa, el toolchain, el manifiesto, los logs de build y axiomas, las fuentes del manuscrito y los inventarios SHA-256. El tag y el commit públicos vinculan esos archivos al nivel del repositorio; el manuscrito no afirma dentro de su texto un identificador de commit.

Los materiales escritos se destinan a distribución bajo CC BY-NC 4.0. El código de verificación y regresión propiedad del autor se destina a distribución bajo PolyForm Noncommercial License 1.0.0; las dependencias de terceros conservan sus propias licencias.

**Límite de la revisión:** la reproducción independiente y la auditoría adversarial externa están completas, y la revisión de novedad está acotada por su corpus. No se han realizado una revisión humana por pares ni una determinación especializada de prioridad. El tag y el commit públicos son metadatos del repositorio y no premisas del teorema.

---

## Apéndice C. Auditorías computacionales

## C.1 LP exacto de perfil común

`verify_common_profile_lp.py` enumera los vértices del poliedro simetrizado de coberturas mediante eliminación gaussiana racional exacta y compara el óptimo con (3.5).

## C.2 Margen fraccional exacto

`verify_fractional_margin.py` comprueba Teorema 4.2 para

\[
3\le p\le80,
\qquad
1\le q\le2p,
\qquad
0\le d\le p
\]

usando aritmética racional exacta.

## C.3 Auditorías ILP pequeñas

`verify_factor_rounding.py` y `verify_shifted_center.py` calculan empaquetamientos integrales exactos de triángulos en instancias pequeñas mediante un ILP binario con capacidades de aristas. Verifican las cotas superiores enunciadas para \(\Phi(G)\).

## C.4 Polarización

`verify_polarization.py` ejecuta comprobaciones exhaustivas de perfiles pequeños y comprobaciones aleatorias con enteros exactos de Lema 6.1.

## C.5 Divisibilidad

`verify_divisibility_correction.py` verifica exhaustivamente la construcción de paridad sobre caminos hasta orden dieciocho, comprueba exactamente el umbral fijo de grado mínimo y sigue la corrección completa de paridad y módulo tres sobre residuales densos aleatorios.

---

### Observación 2.3\(^{\prime}\) — Necesidad de una hipótesis de densidad

**Certificados Lean.** `PaperIII.ax2_divisibility_degree_insufficient`, `PaperIII.ax2_density_necessary_K7_minus_two_triangles`, reexportados mediante `PaperIII.Obstructions`.

### Corolario 10.2b — Término cuadrático afilado y coeficiente lineal forzado

**Certificado Lean.** `PaperIII.Corollary_1_2_sharp`, ensamblado a partir de `PaperIII.Corollary_1_2`, `PaperIII.Byproduct_leading_constant_forced` y `PaperIII.Byproduct_completeSplit_cp_sharp`. La declaración `Byproduct_leading_constant_forced` certifica la afirmación sobre el coeficiente lineal; la sharpness cuadrática se sigue del valor exacto de la familia.

### Corolario E.1.1 — Empaquetamiento por asignación de factores

**Certificado Lean.** `Byproduct_factorization_assignment_packing`.

### Corolario E.1.2 — Cota inferior por doble factorización

**Certificado Lean.** `Byproduct_double_factorization_packing`.

### Corolario E.1.3 — Cota de empaquetamiento con ganancia reservada

**Certificado Lean.** `Byproduct_reserved_gain_packing_bound_subset`.

### Corolario E.2.1 — Constante \(3/2\) del corredor corto

**Certificado Lean.** `Byproduct_short_corridor_constant_three_halves`.

### Corolario E.2.2 — Puente de empaquetamientos a particiones

**Certificados Lean.** `Byproduct_cp_le_Phi`, `Byproduct_low_corridor_cp_three_halves`, `Byproduct_effective_low_corridor_cp_bound`.

### Corolario E.3.1 — Óptimo fraccional exacto

**Certificado Lean.** `Byproduct_commonProfile_tau3Star_eq_F`.

### Corolario E.3.2 — Regiones de fase

**Certificados Lean.** `Byproduct_commonProfile_tau3Star_eq_uniform_region`, `Byproduct_commonProfile_tau3Star_eq_separated_region`, `Byproduct_commonProfile_tau3Star_eq_hot_region`.

### Corolario E.4.1 — Cota inferior para la holgura fraccional

**Certificado Lean.** `Byproduct_unified_fractional_margin`.

### Corolario E.5.1 — Valor exacto y forma normal

**Certificados Lean.** `Byproduct_completeSplit_cp_exact_value`, `Byproduct_completeSplit_cp_sharp`.

### Corolario E.5.2 — Coeficiente lineal forzado

**Certificados Lean.** `Byproduct_leading_constant_forced`, empaquetado con la cota superior y la familia exacta como `Corollary_1_2_sharp`.

### E.6.1 Dualidad LP finita empaquetamiento/cobertura

**Certificados Lean.** `Byproduct_triangle_LP_duality`; forma independiente `Contrib.LPDuality.lp_strong_duality` en `Contrib.LPStrongDuality`.

### E.6.2 Matchings de tipo Dirac y corrección densa

**Certificados Lean.** `Byproduct_dirac_perfect_matching_even`, `Byproduct_dirac_near_perfect_matching`, `Byproduct_dense_divisible_correction_edges`; forma independiente de matching en `Contrib.SpreadMatchingDirac`.

### E.6.3 Interfaz uniforme de nibble

**Certificado Lean.** `Byproduct_almostPerfectMatching_uniform`.

### Corolario E.7.1 — Realización y cota fraccional por aristas

**Certificados Lean.** `Byproduct_nu3_achieved`, `Byproduct_nu3star_le_edges_div_three`.

### Corolario E.7.2 — Forma de brecha de aristas del majority nibble

**Certificado Lean.** `Byproduct_nu3star_sub_nu3_le_edge_gap_most`.

### Apéndice E. Corolarios seleccionados derivados de la formalización

Los nombres de teoremas siguen `PaperIII.PaperImprovements` y el paquete independiente `Contrib.*`. Su estado de release se rige por el gate consolidado de build y axiomas de la Sección 13.

### Corolario E.5.2 — Coeficiente lineal forzado

El certificado más débil `Byproduct_leading_constant_sharp`, que se sigue de inmediato de la forma normal exacta, no se cataloga por separado.

### Corolario 10.2a — Benchmark complete-split exacto

El desarrollo Lean registra la cota superior, la cota inferior y la igualdad como `Byproduct_completeSplit_cp_le_exact_value`, `Byproduct_completeSplit_cp_ge_exact_value` y `Byproduct_completeSplit_cp_exact_value`. El Apéndice E.5 conserva solo la forma normal exacta y el enunciado, lógicamente distinto, sobre el coeficiente lineal forzado.

### E.6.3 Interfaz uniforme de nibble

La biblioteca independiente adjunta también contiene módulos sobre concentración, hamiltonicidad, flujo máximo/corte mínimo, conteo por codegrados, colas hipergeométricas y teoría de diseños. La Sección 11.7 registra su alcance sin presentarlos como corolarios adicionales de este artículo.

### Corolarios en forma de empaquetamiento

Los corolarios siguientes reformulan resultados de las Secciones 5 y 7 directamente en lenguaje de empaquetamientos. Están formalizados como `factorization_assignment_packing`, `double_factorization_packing` y `reserved_gain_packing_bound_subset`. Los tres son incondicionales: ninguno usa el Teorema 2.1 ni el Teorema 2.3.


## Referencias

[1] P. Allen, J. Böttcher, O. Cooley, and R. Mycroft, “Tight cycles and regular slices in dense hypergraphs,” *Journal of Combinatorial Theory, Series A* **149** (2017), 30–100.

[2] B. Barber, D. Kühn, A. Lo, and D. Osthus, “Edge-decompositions of graphs with high minimum degree,” *Advances in Mathematics* **288** (2016), 337–385.

[3] T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, accessed July 6, 2026.

[4] O. V. Borodin, A. V. Kostochka, and D. R. Woodall, “List edge and list total colourings of multigraphs,” *Journal of Combinatorial Theory, Series B* **71** (1997), no. 2, 184–204.

[5] G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

[6] G. A. Dirac, “Some theorems on abstract graphs,” *Proceedings of the London Mathematical Society* (3) **2** (1952), 69–81.

[7] F. Dross, “Fractional triangle decompositions in graphs with large minimum degree,” *SIAM Journal on Discrete Mathematics* **30** (2016), no. 1, 36–42.

[8] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[9] D. Gale and L. S. Shapley, “College admissions and the stability of marriage,” *The American Mathematical Monthly* **69** (1962), no. 1, 9–15.

[10] F. Galvin, “The list chromatic index of a bipartite multigraph,” *Journal of Combinatorial Theory, Series B* **63** (1995), no. 1, 153–158.

[11] P. E. Haxell and V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38.

[12] P. Keevash, “The existence of designs,” arXiv:1401.3665, revised 2018.

[13] D. König, “Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre,” *Mathematische Annalen* **77** (1916), 453–465.

[14] M. Krivelevich, “On a conjecture of Tuza about packing and covering of triangles,” *Discrete Mathematics* **142** (1995), 281–286.

[15] J. P. Traverso Gianini, “Reducción afín de perfiles para empaquetamientos fraccionales de triángulos en grafos split” (Paper I de la serie), preprint, julio de 2026.

[16] J. P. Traverso Gianini, “Extremizadores complete-split para un funcional fraccional de cobertura de triángulos en grafos cordales” (Paper II de la serie), preprint, julio de 2026.

[17] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118.
