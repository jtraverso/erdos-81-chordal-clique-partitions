# Companion de formalización de la estabilidad cordal exacta

**Juan Pablo Traverso Gianini**  
Preprint 1.0, 18 de octubre de 2026. Aplicación formal de los Papers IV y VI. Este companion identifica el paquete final de fuentes, su enunciado público y sus límites de confianza. La nota desarrolla la consecuencia de estabilidad enunciada de los papers fuente; no afirma una nueva solución del Problema 81 de Erdős.

## Enunciado público y alcance

La interfaz pública final es `ChordalStabilityNote.eventual_root_stability`. Afirma que existe un umbral de orden N tal que todo grafo G sobre Fin n, con n al menos N, que satisface cordalidad, `cp G <= Mval n` y `2000 * (Mval n - cp G) <= n`, satisface `RootStability` para el conjunto efectivo definido por grados `{v | n < 2 * G.degree v}`.

La cota superior explícita `cp G <= Mval n` hace que la resta natural coincida con el déficit no negativo del manuscrito. Esta interfaz final no supone un testigo estructural, una cota local de modificación, una fórmula exacta de partición ni una raíz. Todo ello se obtiene en su demostración. El umbral es el máximo entre el umbral del redondeo uniforme y `2 * 10^13`; el término numérico no reemplaza el umbral de redondeo desconocido.

`RootStability` es un registro de conclusiones. Incluye:

| Campo | Conclusión matemática |
|---|---|
| `isClique` | La raíz definida por grados es un clique |
| `exactFormula` | `cp = B(n,p) - A - 2m` sobre los enteros |
| `four` | `cp = cpLe 4` |
| `deficitFormula` | `M-cp = (M-B)+A+2m` |
| `editIdentity` | La distancia de edición a la referencia split completa es igual a `A+m` |
| `editBound` | Esa distancia de edición es a lo sumo `M-cp` |
| `square` | `(6p-2n-1)^2 <= 24(M-cp)+25` |
| `canonical` | La raíz es exactamente el conjunto determinado por el criterio de grados |

La fórmula entera de B evita la resta truncada. La desigualdad cuadrática se expresa sobre los racionales. Estas elecciones conservan el significado aritmético del manuscrito.

## Adaptadores físicos y dependencias de la demostración

`PartitionAdapter` convierte la partición exacta efectiva de IV y la completación de su empaquetamiento físico en la definición de partición en cliques de VI. Identifica las aristas exteriores, las aristas del núcleo y los enlaces ausentes efectivos con las funciones de recuento de VI. Una raíz que es un clique tiene `Cdef = 0`. Estas identificaciones se demuestran; no se introducen como axiomas de interfaz.

`WindowArithmetic` y `GraphWindow` establecen las cotas escalares de entrada, la comparación entre el grado máximo de modificación y la distancia total de edición, y el reconocimiento del núcleo por grados. `PaidRootAssembly` utiliza entonces una partición física y sus cuentas pagadas para invocar el teorema paramétrico efectivo `PaperVI.cp_window_K4` con parámetro cuatro. Este teorema intermedio tiene una hipótesis de raíz pagada, mientras que la interfaz pública final no la tiene.

`NearAssembly` aplica este resultado intermedio a `W.regularized.root` de `NearStructureWitness` de IV. La distinción es esencial: las cuentas físicas pertenecen a la raíz regularizada, no a otro campo denominado core. `FarGap` excluye el régimen lejano comparando la partición completada de un empaquetamiento redondeado efectivo con el óptimo efectivo `cp G`. `GlobalAssembly` proporciona el óptimo fraccional certificado, invoca el redondeo uniforme, obtiene el testigo cercano mediante localización y ensambla la conclusión.

La cadena de demostración seleccionada requiere `uniformTransferAt` de IV, `NearH1Localization.exists_nearStructureWitness_of_nearRegime`, su dependencia de localización por descenso, los adaptadores físicos y la construcción exacta paramétrica de VI. Excluye `PaperIV.Erdos81Unconditional`. La aplicación mantiene su dependencia matemática de IV y VI, aunque tiene su propio proyecto de fuentes y su propia interfaz final. No utiliza el teorema de transferencia del Paper V ni los resultados adicionales de recourse de VI. El cono de entrada de 18 módulos de VI es el subconjunto paramétrico de fuentes congeladas utilizado en esta demostración; la nota principal cita el manuscrito editorial vigente sin afirmar que sus módulos adicionales formen parte de este cono paramétrico de fuentes.

## Validación final y paquete de fuentes

El proyecto utiliza `leanprover/lean4:v4.35.0`, con Mathlib fijada en `56a005855ea17e0b0958f73ec801ae140b0a1679`. Su cierre de fuentes tiene 343 módulos: ocho módulos de esta nota, 317 del cono de fuentes de IV y 18 de la construcción paramétrica de VI. Los módulos heredados de IV conservan su texto fuente y se atribuyen en `AUTHORSHIP_NOTICE.md`. Los módulos propios y controles llevan cabeceras de copyright Apache-2.0; la licencia completa y el aviso de atribución son `lean435/LICENSE` y `lean435/NOTICE`. Los módulos propios y los controles de la nota identifican a Juan Pablo Traverso Gianini como autor. Los módulos de VI están sincronizados con la versión de fuentes con crédito de autor registrada en el manifiesto; los créditos existentes de terceros permanecen sin cambios.

El build de la raíz canónica comprueba `ChordalStabilityNote`. Reutiliza artefactos completos de caché para las dependencias sin cambios, valida sus trazas y recompila las fuentes modificadas. El archivo de fuentes es portable y no contiene cachés ni uniones locales de directorios de desarrollo. Esto no afirma que se hayan recompilado desde cero todos los módulos previos ni Mathlib.

La auditoría completa comprueba primero que todos los módulos del manifiesto de fuentes estén presentes en el entorno Lean importado; la ausencia de un módulo provoca el rechazo.

La auditoría seleccionada de la raíz sigue 7,125 dependencias de declaraciones, exige los insumos estructurales y de redondeo de IV y el teorema paramétrico de VI, y excluye `PaperIV.Erdos81Unconditional`. La auditoría completa del proyecto local cubre 7,393 declaraciones y visita 10,976 dependencias. Ambas permiten únicamente `propext`, `Classical.choice` y `Quot.sound`; no se acepta ningún axioma matemático adicional ni `sorryAx`. `evidence/BUILD_CHECKS.json` registra los comandos y códigos de salida finales. `FINAL_FORMAL_VALIDATION.json` los vincula con las fuentes y las comprobaciones de la entrada pública.

El archivo inmutable es `NOTE_II_LEAN435_FINAL_SOURCE_v1.0.zip`. Su SHA-256 es:

```text
b24c5543d719779568ee9c099d453c170d4c69cbd4a31b293f4ee8375e287531
```

`SOURCE_MANIFEST.json` registra todos los hashes de fuentes y configuración. Su SHA-256 es:

```text
8bcdf425cee099e6e157dffa4356bb720e6fcd47ec138a2d4bac10b710587f75
```

El archivo `lean435/OWNERSHIP_AND_LICENSE.json` enumera, con sus hashes, todas las fuentes Lean propias, incluidos los cortes reutilizados de la serie, que el autor distribuye bajo Apache 2.0. Las cabeceras completas nuevas corresponden a los módulos específicos de esta nota y sus puntos de auditoría; las cabeceras heredadas y las atribuciones matemáticas se conservan. Las dependencias externas mantienen sus propias licencias.

## Reproducción

Extraiga el archivo y ejecute:

```text
cd lean435
lake exe cache get
lake build ChordalStabilityNote
lake env lean -j 1 -s 32768 Endpoint435Gate.lean
lake env lean -j 1 -s 32768 FreezeFullAudit.lean
```

Conserve el archivo `lake-manifest.json` suministrado; el comando de caché obtiene artefactos para las dependencias fijadas sin solicitar una nueva selección de versiones.

El build de la raíz ejecuta la auditoría seleccionada de dependencias y axiomas. El último comando audita el conjunto completo de declaraciones locales importadas. Las dependencias locales están incluidas, de modo que no se requiere una copia de trabajo de los papers principales.

El resultado final conserva explícitamente `cp G <= Mval n`. Sin esta hipótesis, la resta natural podría convertir un déficit matemático negativo en cero. En el manuscrito corresponde a la cota inferior del déficit. La cota superior es `2000 * (Mval n - cp G) <= n`; la división entera no debilita la ventana. El Paper IV proporciona por separado la cota superior eventual. Combinar su umbral con el de esta nota da el corolario escrito correspondiente para grafos cordales suficientemente grandes en la ventana indicada; el resultado congelado conserva la hipótesis explícita de déficit no negativo.

## Correspondencia con el manuscrito y alcance

El argumento formal utiliza objetos efectivos en todo momento. Un empaquetamiento del régimen lejano completado se compara con el óptimo efectivo. El testigo cercano proporciona una raíz regularizada junto con su empaquetamiento físico y sus cuentas. Los adaptadores identifican esas cuentas con las funciones de VI. El teorema de raíz con presupuesto cubierto demuestra la ventana de entrada y aplica la construcción local exacta. Cada campo de `RootStability` es una conclusión, y el criterio de grados identifica la misma raíz al final.

Las fuentes Markdown `CHORDAL_STABILITY_NOTE_v1.0_en.md` y `CHORDAL_STABILITY_NOTE_v1.0_es.md` conservan el teorema, las constantes y las ecuaciones expuestas de la deducción establecida. Este companion describe únicamente el paquete final validado de fuentes. No afirma un teorema de transferencia inversa, un umbral mejorado, una nueva extensión de vértices excepcionales ni una asíntota de conteo.

## Asistencia y responsabilidad

La nota principal conserva la atribución del Paper IV a Claude, de Anthropic, ChatGPT/Codex, de OpenAI, Aristotle, de Harmonic, Certo y Jacobian por el trabajo heredado. La contribución de Aristotle a ese trabajo incluyó la exploración, la búsqueda de contraejemplos, la elaboración de pruebas y su formalización y revisión; no sólo tradujo pruebas terminadas. Para esta nota, ChatGPT/Codex ayudó con el argumento, las interfaces formales, la validación y la presentación; Aristotle aportó una propuesta separada de formalización. Las regresiones de aritmética exacta complementan las comprobaciones de fuentes. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal. La prioridad bibliográfica y la revisión externa son cuestiones separadas.

El autor conserva la responsabilidad por los argumentos, las citas, el código y la presentación. Ningún sistema de IA figura como autor.
