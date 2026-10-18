# De los certificados de realizabilidad a la cota de Erdős 81

**Juan Pablo Traverso Gianini**  
Investigador independiente, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
ORCID: 0009-0003-6068-4096

**Nota de investigación I de la serie, complementaria de los Papers IV y V — Preprint 1.0**  
**Fecha:** 18 de octubre de 2026  
Esta nota reorganiza parte de la demostración del Paper IV mediante la interfaz de transferencia del Paper V. No afirma una nueva solución del Problema 81 de Erdős ni una demostración independiente. El companion formal separado identifica el paquete final de fuentes y sus dependencias.

## Resumen

Reorganizamos parte de la demostración ya establecida de la cota de partición en cliques del Problema 81 de Erdős como una aplicación del teorema de transferencia por clases realizables del Paper V, utilizando el redondeo mixto y las construcciones físicas casi extremales del Paper IV. El certificado pertinente compara la ganancia de un empaquetamiento realizado con una demanda de referencia; su pérdida debe ajustarse al presupuesto de partición del grafo original. Lejos del régimen extremal, una holgura cuadrática paga el redondeo. Cerca de ese régimen, la localización por descenso y las cuentas terminales conservadas del Paper IV proporcionan un empaquetamiento cuya completación ya satisface la cota entera ajustada. Así se recupera la conclusión de IV, para todos los grafos cordales suficientemente grandes de orden \(n\), una partición en cliques de orden a lo sumo cuatro con a lo sumo \(\left\lfloor n(n+1)/6\right\rfloor\) piezas, y un error aditivo absoluto para cualquier orden. El argumento de primera entrada de [7, Sección 8] y el desarrollo de Okechukwu [8] son antecedentes explícitos; aquí se utiliza el descenso de IV. Distinguimos el papel de la transferencia de esa localización estructural y explicamos por qué no es necesario transportar ninguna partición hacia atrás a lo largo del descenso.

## 1. El presupuesto de partición

Una partición en cliques de un grafo simple finito \(G\) particiona \(E(G)\) en los conjuntos de aristas de subgrafos completos de orden al menos dos. Denotamos por \(\operatorname{cp}(G)\) su tamaño mínimo y por \(c_4(G)\) el mínimo correspondiente cuando todas las piezas tienen orden a lo sumo cuatro. Definamos

\[
M(n)=\left\lfloor\frac{n(n+1)}6\right\rfloor.
\tag{1.1}
\]

La pregunta de Erdős, Ordman y Zalcstein [1,4] pide \(\operatorname{cp}(G)\le n^2/6+O(n)\) cuando \(G\) es cordal. El Paper IV [2] demuestra la cota eventual más fuerte \(c_4(G)\le M(n)\), con una corrección aditiva absoluta para los órdenes restantes. Aquí recuperamos esa conclusión mediante el lenguaje de certificados del Paper V [3]. El propósito es identificar la interfaz exacta entre la estructura, la realización física y el número de piezas de la partición. El problema ya está resuelto en IV y en los otros dos desarrollos comparados allí: el preprint firmado Anonymous [7] y Okechukwu [8]. Nuestro propósito es expositivo y organizativo. Conservamos los insumos matemáticos de IV y su atribución, sin ofrecer otra solución independiente.

Para un clique \(Q\), definimos su ganancia mediante

\[
g(Q)=\binom{|Q|}{2}-1.
\]

Si un empaquetamiento \(P\) está formado por cliques disjuntos en aristas, completar individualmente todas las aristas no cubiertas produce una partición de tamaño

\[
e(G)-g(P),\qquad g(P)=\sum_{Q\in P}g(Q).
\tag{1.2}
\]

En efecto, cada clique seleccionado reemplaza tantos bloques individuales como aristas contiene y aporta un bloque en su lugar. La disjunción en aristas permite sumar estos ahorros sin contar ninguna arista dos veces. No se modifica ninguna arista exterior a los cliques seleccionados.

En el modelo mixto utilizado a continuación, las piezas disponibles son triángulos y copias de \(K_4\), con ganancias dos y cinco. Por tanto, una estimación de ganancia proporciona una estimación de partición efectiva sin requerir otro argumento de cobertura. Todos los empaquetamientos obtenidos en esta nota están formados por cliques del grafo original.

## 2. Transferencia con un coste explícito

Utilizamos la siguiente forma de la transferencia por clases realizables del Paper V, con pesos y pérdidas naturales. Tomemos una colección finita de ocurrencias auxiliares ponderadas, de peso total \(D\), eliminemos ocurrencias de peso total \(z\) y particionemos las restantes en \(q\ge1\) clases. Para cada clase \(i\), construyamos un empaquetamiento físico \(P_i\) en \(G\) y una pérdida no negativa \(r_i\) tales que

\[
\text{peso de la clase }i\le g(P_i)+r_i.
\tag{2.1}
\]

Las clases no tienen que ser independientes en el grafo auxiliar de conflictos. La factibilidad se exige a sus realizaciones físicas. Sea \(C=z+\sum_i r_i\). Sumando (2.1), alguna clase satisface

\[
g(P_i)\ge\frac{D-C}{q}.
\tag{2.2}
\]

Las clases restantes tienen peso total \(D-z\). Al sumar sus desigualdades de realización se obtiene \(\sum_i g(P_i)\ge D-z-\sum_i r_i=D-C\). Al menos una de las \(q\) ganancias es mayor o igual que su promedio. Elegimos ese único empaquetamiento; no tomamos la unión de los empaquetamientos, que pueden compartir aristas.

Este es el teorema de transferencia por clases realizables [3]. Con \(L=D/q\) y \(\rho=C/q\), la completación da

\[
c_4(G)\le e(G)-L+\rho.
\tag{2.3}
\]

**Proposición 2.1.** Un certificado cuyas salidas físicas son triángulos y copias de \(K_4\) demuestra \(c_4(G)\le T\) siempre que

\[
qe(G)+C\le qT+D.
\tag{2.4}
\]

**Demostración.** Elijamos la salida de (2.2). Su completación tiene tamaño a lo sumo \(e(G)-D/q+C/q\), que por (2.4) es a lo sumo \(T\).

Resulta útil comparar con el óptimo fraccional mixto \(W^*(G)\). Si \(L\le W^*(G)\), definamos

\[
\Delta=M(n)-e(G)+W^*(G),\qquad
\gamma=W^*(G)-L.
\]

La ecuación (2.3) se convierte en

\[
c_4(G)\le M(n)-\Delta+\gamma+\rho.
\tag{2.5}
\]

Para ver la cancelación, sustituyamos \(L=W^*(G)-\gamma\) en (2.3) y utilicemos después \(e(G)-W^*(G)=M(n)-\Delta\). Las dos pérdidas quedan medidas respecto del mismo presupuesto: \(\gamma\) es la diferencia entre el óptimo fraccional y la demanda de referencia por clase, mientras que \(\rho\) es el coste de realización por clase.

La condición suficiente es \(\gamma+\rho\le\Delta\). Una cota uniforme de la brecha de integralidad para todo grafo cordal es más fuerte de lo que requiere esta aplicación. El certificado solo debe ajustarse al margen del grafo considerado. Escribir (2.5) no proporciona, por sí solo, ni un defecto de coloreabilidad pequeño ni una realización de bajo coste.

Para el ensamblaje final utilizamos una clase. Fijemos una referencia entera \(R\) antes de construir la salida. Si un empaquetamiento físico \(P\) satisface \(g(P)\le R\), una única demanda auxiliar de peso \(R\) se realiza mediante \(P\) con pérdida \(R-g(P)\). Su certificado satisface (2.4) exactamente cuando

\[
e(G)+R-g(P)\le T+R.
\tag{2.6}
\]

La referencia \(R\) se cancela de ambos lados de (2.6). Esta condición es, por tanto, precisamente \(e(G)-g(P)\le T\), el coste de completación ya identificado en (1.2). La hipótesis \(g(P)\le R\) garantiza que la pérdida registrada sea no negativa.

La elección \(R=e(G)\) sirve para cualquier empaquetamiento disjunto en aristas, pues \(g(P)\le e(G)\). Esta especialización expresa una construcción física previamente establecida mediante la interfaz de transferencia; no mejora esa construcción por promediación. El enunciado general para \(q\) clases sigue siendo útil cuando se dispone de varias realizaciones, pero la deducción que sigue no necesita una mejora de ese tipo.

## 3. Los resultados de entrada del Paper IV

Para precisar las dependencias, enunciamos los dos resultados combinatorios de entrada independientemente del teorema final de partición cordal. Sus demostraciones pertenecen al Paper IV. Sea \(W^*(G)\) la ganancia fraccional mixta máxima, con capacidad uno en cada arista. Puesto que se trata de un programa lineal racional finito, el máximo se alcanza con un certificado primal-dual racional.

**Resultado de entrada 3.1.** Para todo \(\zeta>0\) existe \(N_\zeta\) tal que todo grafo \(G\) de orden \(n\ge N_\zeta\) tiene un empaquetamiento físico \(P\) de triángulos y copias de \(K_4\) que satisface

\[
W^*(G)-g(P)\le\zeta n^2.
\tag{3.1}
\]

La interfaz formal recibe una tolerancia racional positiva. Esto basta para la tolerancia real enunciada: se elige un racional positivo menor que \(\zeta\) y se aplica la interfaz a ese número. El error resultante también es a lo sumo \(\zeta n^2\).

El Resultado de entrada 3.1 es exactamente el caso \(r=4\) del Teorema 3.4 de Rohatgi–Urschel–Wellens [11]: sus objetivos integral y fraccional asignan a cada clique la ganancia \(\binom{|Q|}{2}-1\), que aquí vale dos o cinco. Su pérdida uniforme es \(o(n^2)\). Haxell–Rödl [9] y Yuster [10, Teorema 1.2] son los antecedentes de transferencia citados allí. El proyecto formal de esta nota utiliza la implementación demostrada del Paper IV [2, Teorema 3.1], construida con la infraestructura del Paper III; no se afirma un enunciado de redondeo más fuerte que [11] para esta aplicación. La pérdida subcuadrática basta en el régimen lejano y no es una cota de error lineal. La cordalidad interviene en el segundo resultado de entrada.

**Resultado de entrada 3.2.** Existe un \(\eta>0\) absoluto tal que, para todo grafo cordal \(G\) suficientemente grande que satisfaga

\[
e(G)-W^*(G)\ge\frac{n^2}{6}-\eta n^2,
\tag{3.2}
\]

la construcción casi extremal proporciona un empaquetamiento físico \(P\) de triángulos y copias de \(K_4\) en \(G\) y cantidades no negativas \(m\) y \(A\) tales que

\[
e(G)-g(P)\le B(n,p)-\frac m{20}-\frac A2,
\qquad
B(n,p)=p(n-p)-\binom p2,
\tag{3.3}
\]

donde \(p\) es un entero entre cero y \(n\). Aquí \(m\) y \(A\) son los recuentos efectivos de aristas exteriores y enlaces ausentes en las cuentas físicas conservadas, respecto de la raíz regularizada. No son errores indeterminados introducidos después de la construcción.

La calibración formal concreta utiliza \(\eta=10^{-16}\) y \(n\ge4\cdot10^{12}\) para el Resultado de entrada 3.2. No optimizamos estas constantes. El Resultado de entrada 3.1 puede requerir un umbral mucho mayor.

El Resultado de entrada 3.2 combina [2, Proposición 4.3, Teorema 5.0 y Lema 5.3, ecuación (5.15)]. Su demostración tiene dos salidas distintas. El descenso mediante copias de vértices localiza el grafo original cerca de un grafo split completo de comparación. La regularización de la raíz y la construcción terminal producen después el empaquetamiento y las cuentas de (3.3), directamente en \(G\). Esta distinción importa: el descenso se utiliza para establecer estructura, no para transportar una sucesión de particiones de vuelta a \(G\).

## 4. La deducción de Erdős 81

Recordemos primero la cota entera para el valor de referencia split. Completando el cuadrado se obtiene

\[
B(n,p)=\frac{(2n+1)^2}{24}
-\frac{(6p-2n-1)^2}{24}
\le\frac{n(n+1)}6+\frac1{24}.
\tag{4.1}
\]

El primer numerador es \(4n(n+1)+1\), lo que produce el término final \(1/24\). El cuadrado sustraído es no negativo para todo entero \(p\); la estimación no requiere, por tanto, elegir un núcleo extremizante.

El número \(B(n,p)\) es entero. La parte fraccionaria de \(n(n+1)/6\) es múltiplo de \(1/6\), de modo que sumar \(1/24\) no puede alcanzar el entero siguiente. En consecuencia,

\[
B(n,p)\le M(n).
\tag{4.2}
\]

**Teorema 4.1.** Suponiendo los Resultados de entrada 3.1 y 3.2, existe \(N\) tal que todo grafo cordal \(G\) de orden \(n\ge N\) admite una partición en cliques con todas sus piezas de orden a lo sumo cuatro y con a lo sumo \(M(n)\) piezas.

**Demostración.** Apliquemos el Resultado de entrada 3.1 con \(\zeta=\eta/2\) y tomemos \(N\) suficientemente grande para ambos resultados de entrada. Escribamos \(W^*=W^*(G)\). Hay dos casos. La tolerancia se elige antes del grafo: un único umbral, el máximo de los dos umbrales de entrada, sirve para todos los grafos considerados a continuación.

Si \(e(G)-W^*<n^2/6-\eta n^2\), el Resultado de entrada 3.1 proporciona un empaquetamiento físico \(P\) que satisface

\[
e(G)-g(P)
\le e(G)-W^*+\frac\eta2n^2
<\frac{n^2}{6}-\frac\eta2n^2
\le\frac{n(n+1)}6.
\tag{4.3}
\]

La primera desigualdad suma la pérdida de redondeo al coste fraccional de completación. La desigualdad estricta del régimen lejano proporciona el doble de la pérdida de redondeo permitida, por lo que se conserva la mitad de ese margen. La comparación final solo utiliza \(n\ge0\).

Como \(e(G)-g(P)\) es entero, es a lo sumo \(M(n)\). Por tanto, el certificado de una clase de la Sección 2, con \(R=e(G)\), satisface (2.4) para \(T=M(n)\). La Proposición 2.1 da la partición requerida.

En caso contrario se cumple (3.2). El Resultado de entrada 3.2 proporciona un empaquetamiento físico con

\[
e(G)-g(P)\le B(n,p)-\frac m{20}-\frac A2
\le B(n,p)\le M(n).
\tag{4.4}
\]

La desigualdad intermedia descarta dos créditos no negativos, \(m/20\) y \(A/2\); la última utiliza la cota entera de referencia (4.2). Las tres estimaciones se refieren al mismo empaquetamiento proporcionado por el Resultado de entrada 3.2. El mismo certificado y la Proposición 2.1 concluyen este caso. Todos los cliques seleccionados tienen orden tres o cuatro, y la completación solo añade piezas \(K_2\).

**Corolario 4.2.** Existe un entero absoluto \(b\ge0\) tal que todo grafo cordal \(G\) de cualquier orden \(n\) satisface

\[
\operatorname{cp}(G)\le c_4(G)\le M(n)+b
\le\frac{n^2}{6}+\frac n6+b.
\tag{4.5}
\]

**Demostración.** Sea \(N\) como en el Teorema 4.1 y tomemos \(b=N^2\). Para \(n\ge N\) utilizamos el teorema. Para \(n<N\), las aristas individuales forman una partición con a lo sumo \(\binom n2\le N^2\) piezas. El grafo vacío también satisface la cota. Para \(n\ge1\), la última expresión de (4.5) es a lo sumo \(n^2/6+(b+1/6)n\); en \(n=0\) no se necesitan piezas. Esta es la cota solicitada en el Problema 81 de Erdős.

La conclusión ya está establecida en el Paper IV; esta nota proporciona un ensamblaje explícito de transferencia a partir de sus resultados estructurales y de redondeo. No demuestra que \(b=0\) para todos los órdenes ni un umbral mejorado.

## 5. Qué reemplaza la transferencia

Tres preguntas aparecen en distintas etapas del argumento. La localización pregunta por qué un grafo cordal casi extremal tiene una raíz útil. La realización pregunta cómo convertir demandas auxiliares en cliques del grafo original. La completación pregunta si la ganancia de esos cliques paga el número de piezas de partición deseado.

El teorema de transferencia aborda las dos últimas preguntas una vez proporcionadas las realizaciones y sus pérdidas. Puede reemplazar una conversión basada en coloreabilidad cuando las clases admiten realizaciones físicas de menor coste. Por sí solo no encuentra una raíz ni demuestra (3.3). Por tanto, no reemplaza el papel estructural de la copia de vértices ni de la desestabilización en esta deducción.

La primera entrada utilizada en [7, Sección 8], y comparada con IV en [2, Sección 8], es un argumento de localización: se sigue un camino de copias y se identifica su primera visita a un entorno prescrito de la familia split. En cambio, la implementación utilizada para el Resultado de entrada 3.2 invoca el teorema existente de localización por descenso. Esta elección evita un selector de primera entrada en la cadena de demostración seleccionada. Se trata de una propiedad del resultado estructural de entrada, no de una consecuencia de la desigualdad abstracta de transferencia. Algunos módulos fuente también contienen el desarrollo alternativo de primera entrada; importarlos no significa que su selector sea una premisa del teorema utilizado aquí.

Conservar las cuentas físicas ofrece una ventaja relacionada. Si cada paso de copia exigiera transportar una partición hacia atrás, las pérdidas podrían acumularse a lo largo del camino. La ruta anterior primero localiza \(G\) y después construye su empaquetamiento una sola vez. La pérdida que paga el certificado de transferencia es la de esta realización final. La longitud del camino de copias no aparece como un coste adicional de partición.

## 6. Lugar en la serie

Los Papers I y II desarrollan el marco de perfiles y estructura fraccional; el Paper III proporciona las herramientas de empaquetamiento estructurado y redondeo. El Paper IV establece la localización y las construcciones físicas requeridas aquí. El Paper V separa el enunciado general de transferencia y su coste de realizabilidad. Esta nota hace explícita la interfaz entre los dos últimos papers, conservando la atribución del trabajo anterior.

La nota documenta una organización alternativa de parte de la demostración de IV para la entrega que acompaña al Paper V. No es una segunda demostración matemáticamente independiente de la cota extremal. El cálculo del presupuesto y el proyecto formal separado documentan precisamente cómo su teorema de certificados recupera la cota establecida a partir de las construcciones de IV.

El ejemplo también delimita el alcance de una afirmación de aplicación. Volver a expresar un buen empaquetamiento como un certificado de una clase establece su compatibilidad con el mecanismo, pero no demuestra que este haya aportado nuevos ahorros combinatorios. Una aplicación más fuerte construiría realizaciones de bajo coste directamente a partir de información estructural más débil. Esa sigue siendo una dirección de investigación separada.

## Formalización y reproducibilidad

El proyecto separado en Lean 4.35 formaliza el adaptador de transferencia física y el ensamblaje a partir de los insumos demostrados de IV y V. Su auditoría de dependencias seleccionadas comprueba el uso efectivo de la transferencia por clases realizables de V y de la localización por descenso de IV, y excluye el teorema final de cota global de IV. Esta exclusión describe el ensamblaje, no una independencia matemática respecto de IV. El companion formal identifica el paquete final congelado de fuentes, la auditoría completa de axiomas locales, las interfaces públicas y los comandos de reproducción. [Fuentes y companion formal](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/series_notes/NOTE_I_ERDOS81_TRANSFER/05_formalization).

## Agradecimientos

El autor agradece profundamente a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín su amor, paciencia y apoyo.

## Uso de inteligencia artificial y herramientas computacionales

En los artículos fuente utilizados aquí, se utilizaron Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, para explorar argumentos, comprobarlos y preparar los manuscritos. Aristotle, de Harmonic, participó en la exploración de caminos, la búsqueda de contraejemplos, la elaboración de pruebas y su formalización y revisión en Lean; no sólo tradujo pruebas terminadas.

Para esta nota, ChatGPT/Codex ayudó a ensamblar el argumento de las fuentes, construir y comprobar los adaptadores Lean y preparar la exposición y la auditoría interna.

Certo [5] y Jacobian [6] son las herramientas computacionales usadas en el programa de investigación subyacente para explorar instancias, comprobar identidades y evaluar candidatos, según se declara en el Paper IV. Su uso se declara por separado de las dependencias lógicas de la prueba formal. El companion separado y los registros de auditoría identifican las comprobaciones realizadas específicamente para esta nota, incluidas sus pruebas de regresión en Python. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal.

El autor conserva la responsabilidad por los argumentos, las citas, el código y la presentación. Ningún sistema de IA figura como autor.

## Referencias

[1] P. Erdős, E. T. Ordman y Y. Zalcstein, “Clique partitions of chordal graphs,” Combinatorics, Probability and Computing 2 (1993), 409–415. <https://doi.org/10.1017/S0963548300000808>.

[2] J. P. Traverso Gianini, Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds, Paper IV, preprint v1.23, 1 de octubre de 2026. La versión conservada en la distribución de la serie es la fuente de los Resultados de entrada 3.1 y 3.2. [Manuscrito y materiales](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/054593443bdece587dda9686a411bb18b0ca34c5/preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_en.md). Depósito: [doi:10.5281/zenodo.23089131](https://doi.org/10.5281/zenodo.23089131).

[3] J. P. Traverso Gianini, Colorability and Realizability Defects in Resource-Dominated Packing Relaxations, Paper V, Preprint 1.0 y paquete formal de fuentes complementario, 18 de octubre de 2026. El teorema de transferencia por clases realizables es el resultado utilizado en la Sección 2. [Manuscrito y materiales](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_V).

[4] T. F. Bloom, “Erdős Problem #81,” Erdős Problems, https://www.erdosproblems.com/81. Se cita para identificar el problema; esta nota no certifica el estado actual de revisión externa de las soluciones propuestas.

[5] J. P. Traverso Gianini, *Certo: herramientas computacionales con certificados verificables*. [Manuscrito y materiales](https://github.com/jtraverso/certo-math).

[6] Morluto y colaboradores, *Jacobian: herramientas matemáticas componibles*. [Manuscrito y materiales](https://github.com/morluto/jacobian).


[7] Anonymous, *Clique partitions of chordal graphs with linear error*, preprint, 8 de septiembre de 2026. Versión comparada en el Paper IV: commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. [Manuscrito y materiales](https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/manuscript/main.pdf). Se conserva la firma del manuscrito. El README de ese commit atribuye la demostración matemática a Morluto y el manuscrito y la implementación Lean a N0zoM1z0, con Jacobian de Preference Labs como parte del proyecto; estos créditos se distinguen de la autoría impresa.

[8] O. Okechukwu, *Clique partitions and bounded simplicial defect*, arXiv:2609.20871v1, 15 de septiembre de 2026. <https://arxiv.org/abs/2609.20871v1>. La comparación y el alcance utilizados aquí son los documentados en el Paper IV, Sección 8.1.

[9] P. E. Haxell y V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38. <https://doi.org/10.1007/s004930170003>.

[10] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118. <https://doi.org/10.1002/rsa.20048>.

[11] D. Rohatgi, J. C. Urschel, y J. Wellens, “Regarding Two Conjectures on Clique and Biclique Partitions,” *Electronic Journal of Combinatorics* **28**(4) (2021). <https://doi.org/10.37236/9564>. Versión de los autores: <https://arxiv.org/abs/2005.02529>.
