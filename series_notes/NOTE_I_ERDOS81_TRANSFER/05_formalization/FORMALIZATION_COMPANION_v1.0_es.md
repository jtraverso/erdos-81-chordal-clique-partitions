# Companion formal de la nota de transferencia de Erdős 81

**Juan Pablo Traverso Gianini**  
Ensamblaje formal de la aplicación IV–V  
Preprint 1.0, 18 de octubre de 2026

Este companion describe el paquete final de fuentes Lean de la Nota de investigación I de la serie, Preprint 1.0. La nota reorganiza parte de la demostración del Paper IV mediante la interfaz de transferencia del Paper V. No afirma una nueva solución del Problema 81 de Erdős ni una demostración matemáticamente independiente. Los enunciados y términos de demostración conservan su alcance establecido. La validación actual queda vinculada al manifiesto de fuentes y a los registros finales identificados más abajo.

## 1. Qué demuestra la formalización

Las conclusiones públicas producen particiones efectivas en cliques del grafo original. Para todos los grafos cordales suficientemente grandes de orden \(n\), la partición tiene a lo sumo

\[
M(n)=\left\lfloor\frac{n(n+1)}6\right\rfloor
\]

bloques, cada uno con a lo sumo cuatro vértices. Para todos los órdenes, incluido cero, basta una constante aditiva absoluta. Esta aplicación no afirma la cota ajustada para cada orden, una cota superior numérica del umbral eventual ni un nuevo valor extremal.

El módulo raíz es `Erdos81Note.lean`. Importa `Erdos81Note.Assembly`, que importa directamente el adaptador de transferencia física y los resultados requeridos de IV. El ensamblaje invoca el teorema efectivo de transferencia por clases realizables de V. No invoca la cota final de IV para todos los grafos cordales. El proyecto mantiene su dependencia matemática de los resultados estructurales y de redondeo de IV y del teorema de transferencia de V; el proyecto separado documenta otro ensamblaje de esos insumos demostrados. El Paper VI no es un resultado de entrada.

La nota principal conserva un párrafo sobre formalización. Este companion detalla los límites del modelo, las seis interfaces públicas comprobadas, la cadena de dependencias seleccionada, la auditoría completa de axiomas del proyecto local y la información de reproducción.

## 2. Grafos, recursos y aritmética entera

El modelo de grafo físico es `SimpleGraph V`, con un tipo finito de vértices, igualdad decidible y adyacencia decidible. Las dos primeras interfaces públicas funcionan sobre un tipo finito arbitrario. Los teoremas finales de grafos utilizan `Fin n`. La cordalidad es el predicado `PaperIV.IsChordal G`, que se imprime como `G.IsChordal` en el control de interfaces finales.

Un elemento de empaquetamiento es un conjunto finito de vértices que forma un clique y tiene cardinalidad tres o cuatro. Sus recursos son sus pares no ordenados de vértices distintos, es decir, aristas efectivas del grafo. Un empaquetamiento está formado por elementos de este tipo con soportes de aristas disjuntos. Su ganancia, de valor natural, es

\[
g(P)=\sum_{Q\in P}\left(\binom{|Q|}{2}-1\right).
\]

El adaptador `physicalCS` hace que dos elementos distintos estén en conflicto precisamente cuando sus soportes de aristas se solapan. Las aplicaciones `toPacking` y `liftPacking` demuestran la correspondencia entre las salidas factibles de V y los empaquetamientos físicos de IV; sus lemas de ganancia conservan la suma ponderada. Este paso descarta un certificado cuya supuesta realización sea solo un objeto auxiliar sin aristas del grafo.

Una `CliquePartition G` contiene una familia finita de cliques, cada uno de orden al menos dos, con soportes de aristas disjuntos dos a dos cuya unión es exactamente `G.edgeFinset`. `Q.size` cuenta bloques y `Q.OrderAtMost 4` acota sus órdenes. La completación añade un bloque de dos vértices por cada arista no cubierta y demuestra

\[
|Q|+g(P)=e(G).
\]

Por tanto, la resta utilizada en la interfaz de empaquetamiento pagado es una resta natural con la cota demostrada \(g(P)\le e(G)\); no es una truncación sin justificar. Del mismo modo, `targetSize n` es la división natural \(n(n+1)/6\), exactamente \(M(n)\).

El predicado racional `CertifiedFractionalOptimum G w` significa que existen un empaquetamiento fraccional mixto factible y una cobertura dual factible, ambos de valor \(w\). Proporciona testigos primal y dual coincidentes, en lugar de una afirmación sin soporte de que existe un máximo. El ensamblaje obtiene este certificado del teorema de existencia demostrado en IV antes de separar los casos lejano y cercano.

## 3. Las seis interfaces públicas comprobadas

Todos los nombres de esta sección pertenecen al espacio de nombres `Erdos81Note`. El control de interfaces finales comprueba sus tipos elaborados completos e imprime sus dependencias axiomáticas. La salida original se conserva como `evidence/ENDPOINTS.log`; las descripciones siguientes mantienen todas las hipótesis y conclusiones sustantivas.

### 3.1. `partition_of_certificate`

Sea \(G\) un grafo simple finito cualquiera, sea \(C\) un sistema auxiliar de conflictos y sean naturales los valores de la función de pesos \(w\), la función de multiplicidades \(X\), el número de clases \(q\) y el objetivo \(T\). Supongamos \(1\le q\) y un certificado

\[
\texttt{RealCert}\bigl(C,\operatorname{physicalCS}(G),
w,\operatorname{physicalWeight}(G),X,q\bigr).
\]

El certificado incluye las ocurrencias eliminadas, una asignación de las restantes a clases y una realización física factible para cada clase, con una pérdida natural explícitamente acotada. Su coste es el peso eliminado más la suma de las pérdidas de realización. Si

\[
q\,e(G)+\operatorname{cost}(\mathrm{cert})
\le qT+\operatorname{wMultSize}(C,w,X),
\]

entonces existe una `CliquePartition G` de orden a lo sumo cuatro y tamaño a lo sumo \(T\). No se requiere una hipótesis de cordalidad. La demostración invoca `PaperV.realizable_class_transfer`, convierte la realización seleccionada en un empaquetamiento físico y lo completa.

### 3.2. `partition_of_paid_packing`

Para cualquier grafo finito \(G\), objetivo natural \(T\) y empaquetamiento físico mixto \(P\), supongamos

\[
e(G)-g(P)\le T.
\]

Entonces existe una partición en cliques de \(G\), de orden a lo sumo cuatro y tamaño a lo sumo \(T\). Internamente, la demostración elige una ocurrencia auxiliar de peso de referencia \(e(G)\), una clase y una pérdida de realización \(e(G)-g(P)\), y aplica la interfaz precedente. La construcción expresa un empaquetamiento físico pagado en el lenguaje de transferencia; no afirma un ahorro adicional por promediación.

### 3.3. `far_certificate`

Para todo racional \(\eta>0\) existe un umbral natural \(N\) tal que, para todo \(n\ge N\), todo grafo \(G\) sobre `Fin n` y todo óptimo racional certificado \(w\), la desigualdad

\[
e(G)-w<\frac{n^2}{6}-\eta n^2
\]

implica una partición en cliques de orden a lo sumo cuatro y tamaño a lo sumo \(M(n)\). Esta interfaz **no** requiere cordalidad. Utiliza la transferencia uniforme de IV con parámetro \(\eta/2\); el margen del régimen lejano paga la pérdida de redondeo. Su umbral es existencial, no el umbral explícito de la rama cercana que aparece a continuación.

### 3.4. `near_certificate`

Sea \(n\ge4\cdot10^{12}\), sea \(G\) un grafo cordal sobre `Fin n` y sea \(w\in\mathbb Q\) con un testigo de óptimo fraccional certificado. Supongamos la negación de la desigualdad estricta del régimen lejano:

\[
\neg\left(e(G)-w<\frac{n^2}{6}-\eta n^2\right),
\qquad \eta=10^{-16}.
\]

Entonces existe una partición en cliques de orden a lo sumo cuatro y tamaño a lo sumo \(M(n)\). La demostración obtiene un testigo efectivo de estructura cercana mediante la localización por descenso de IV, utiliza su empaquetamiento físico y sus cuentas conservadas, demuestra que su completación está pagada e invoca `partition_of_paid_packing`. Esta interfaz no supone ni una cota objetivo para la partición ni un testigo de raíz preexistente.

### 3.5. `erdos81_eventual`

Existe \(N\in\mathbb N\) tal que, para todo \(n\ge N\) y todo grafo cordal \(G\) sobre `Fin n`, existe una partición en cliques de orden a lo sumo cuatro y tamaño a lo sumo \(M(n)\). El óptimo certificado y la separación de casos se obtienen internamente. El umbral elegido es el máximo entre el umbral de la rama lejana para \(\eta=10^{-16}\) y \(4\cdot10^{12}\); no se afirma que este último baste por sí solo para el teorema global.

### 3.6. `erdos81_all_orders`

Existe \(b\in\mathbb N\) tal que, para todo \(n\in\mathbb N\) y todo grafo cordal \(G\) sobre `Fin n`, existe una partición en cliques de orden a lo sumo cuatro y tamaño a lo sumo \(M(n)+b\). La demostración toma \(b=N^2\) del teorema anterior. Por debajo del umbral utiliza aristas individuales; por encima, el teorema eventual. Ninguna hipótesis de orden positivo excluye el grafo vacío.

## 4. Resultados utilizados y resultados excluidos

La rama lejana invoca `PaperIV.RC01FarAssembly.uniformTransferAt`. La rama cercana invoca `PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime` y alcanza la declaración de localización por descenso `PaperIV.LocalStability.localize_original_of_windowed_accounts_descent`. La existencia del óptimo la proporciona `PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum`.

La auditoría de la cadena de demostración seleccionada comienza con la interfaz de certificados y las dos cotas finales. Sigue los tipos de declaraciones y los términos de prueba a través de la serie local y registra 6,528 declaraciones visitadas. Exige dependencias efectivas de la transferencia de V y de la localización por descenso de IV. Rechaza declaraciones procedentes de `PaperIV.Erdos81Unconditional`, el módulo de la cota global final. Tanto la lista registrada de dependencias prohibidas como las coincidencias normalizadas de primera entrada están vacías.

Esta afirmación concierne a las dependencias de la demostración seleccionada; no afirma que todos los archivos fuente importados omitan argumentos alternativos. Algunos archivos previos contienen desarrollos de primera entrada no utilizados. Su presencia en un paquete fuente no convierte esas declaraciones en premisas de la aplicación final. La lista completa de dependencias se conserva como `DECLARATION_DEPENDENCIES.txt`.

La partición física se construye una sola vez en el grafo original después de la localización. La formalización no transporta particiones hacia atrás a lo largo de pasos de copia de vértices ni cobra una pérdida adicional por paso. El teorema de certificados organiza el presupuesto de ganancia; la localización estructural y la construcción física siguen correspondiendo a IV.

## 5. Validación final y límites de confianza

El proyecto canónico utiliza `leanprover/lean4:v4.35.0` y el commit de Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. El cierre de fuentes contiene 324 módulos locales. La validación final consta del build de la raíz, el control de seis interfaces y la auditoría completa del proyecto local. El build utiliza artefactos completos de caché, con trazas comprobadas, para las dependencias sin cambios y recompila los módulos modificados; no se describe como una recompilación desde cero de todas las fuentes previas ni de Mathlib.

La auditoría seleccionada de la raíz recorre 6,528 dependencias de declaraciones. Comprueba el uso efectivo de la transferencia de V y de la localización por descenso de IV y excluye el módulo final de cota global de IV. La auditoría completa cubre 6,850 declaraciones locales y visita 10,304 dependencias. Son alcances distintos: la segunda incluye los auxiliares privados y las demás declaraciones de todos los módulos locales importados.

La auditoría completa comprueba primero que todos los módulos del manifiesto de fuentes estén presentes en el entorno Lean importado; la ausencia de un módulo provoca el rechazo.

La unión permitida de axiomas es `propext`, `Classical.choice` y `Quot.sound`. Los controles rechazan axiomas matemáticos adicionales y `sorryAx`. Los códigos de salida satisfactorios y los registros de comandos se documentan en `evidence/BUILD_CHECKS.json`; `FINAL_FORMAL_VALIDATION.json` vincula esos registros con el cierre exacto de fuentes y las comprobaciones de la entrada pública.

El autor de la formalización de la nota es Juan Pablo Traverso Gianini. Los módulos propios y los controles identifican al autor en sus cabeceras. `AUTHORSHIP_NOTICE.md` reconoce los cortes heredados de fuentes de la serie sin alterar sus atribuciones matemáticas y de asistencia existentes. Las dependencias de Paper V utilizan la versión de fuentes con crédito de autor registrada en el manifiesto. Los módulos propios y controles de la nota se distribuyen bajo Apache License 2.0, con el texto completo en `lean435/LICENSE` y la atribución en `lean435/NOTICE`. Se conservan las licencias y atribuciones heredadas.

El archivo `lean435/OWNERSHIP_AND_LICENSE.json` enumera, con sus hashes, todas las fuentes Lean propias, incluidos los cortes reutilizados de la serie, que el autor distribuye bajo Apache 2.0. Las cabeceras completas nuevas corresponden a los módulos específicos de esta nota y sus puntos de auditoría; las cabeceras heredadas y las atribuciones matemáticas se conservan. Las dependencias externas mantienen sus propias licencias.

## 6. Reproducción y paquete inmutable

Extraiga `NOTE_I_LEAN435_FINAL_SOURCE_v1.0.zip`, entre en `lean435` y ejecute:

```text
lake exe cache get
lake build Erdos81Note
lake env lean -j 1 -s 32768 Endpoint435Gate.lean
lake env lean -j 1 -s 32768 FreezeFullAudit.lean
```

Conserve el archivo `lake-manifest.json` suministrado; el comando de caché obtiene artefactos para las dependencias fijadas sin solicitar una nueva selección de versiones.

El build de la raíz ejecuta la auditoría seleccionada de dependencias de `Erdos81Note.lean`. El control de interfaces imprime los seis tipos públicos y sus dependencias de axiomas. La auditoría completa comprueba cada declaración del cierre local importado. El archivo incluye todas las fuentes locales requeridas y la configuración con versiones fijadas; excluye las cachés `.lake` y las uniones de directorios de desarrollo. El paquete no requiere una copia de trabajo de los Papers IV o V.

El SHA-256 del archivo de fuentes es:

```text
eae69a0316113f1701246b54243a1b51696b85ea656309319b8738932f90f604
```

`SOURCE_MANIFEST.json` contiene el hash de cada fuente y archivo de configuración empaquetados. Su propio SHA-256 es:

```text
5f7deb401e26fcce100d576e4ed5c6975a46d14265144a1f267439b67f24613f
```

`FINAL_FORMAL_VALIDATION.json` registra los resultados de build, exportación y axiomas de este paquete. Los scripts de regresión de aritmética exacta son comprobaciones complementarias, no premisas de los teoremas universales.

## Asistencia y alcance

La nota principal conserva la atribución del Paper IV a Claude, de Anthropic, ChatGPT/Codex, de OpenAI, Aristotle, de Harmonic, Certo y Jacobian por el trabajo heredado. La contribución de Aristotle a ese trabajo incluyó la exploración, la búsqueda de contraejemplos, la elaboración de pruebas y su formalización y revisión; no sólo tradujo pruebas terminadas. Para esta nota, ChatGPT/Codex ayudó con los adaptadores, la verificación y la presentación del paquete final. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal. La verificación por el kernel no establece prioridad histórica ni sustituye la revisión externa.

El autor conserva la responsabilidad por los argumentos, las citas, el código y la presentación. Ningún sistema de IA figura como autor.
