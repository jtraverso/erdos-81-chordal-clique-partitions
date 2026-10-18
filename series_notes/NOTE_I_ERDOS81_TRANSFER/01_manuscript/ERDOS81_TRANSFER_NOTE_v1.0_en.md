# From realizability certificates to the Erdős 81 bound

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
ORCID: 0009-0003-6068-4096

**Series research note I, accompanying Papers IV and V — Preprint 1.0**  
**Date:** October 18, 2026  
This note reorganizes part of the proof in Paper IV through the transfer interface of Paper V. It claims neither a new solution of Erdős Problem 81 nor an independent proof. The separate formal companion identifies the final source package and its dependencies.

## Abstract

We reorganize part of the already established proof of the clique-partition bound in Erdős Problem 81 as an application of the realizable-class transfer theorem of Paper V, using the mixed rounding and near-extremal physical constructors of Paper IV. The relevant certificate compares the gain of a realized packing with a reference demand; its loss must fit the partition budget of the original graph. Quadratic slack pays for rounding away from the extremal regime. Near that regime, the descent localization and retained terminal accounts of Paper IV supply a packing whose completion already fits the sharp integer bound. This recovers the conclusion of IV, for all sufficiently large chordal graphs of order \(n\), a partition into cliques of order at most four with at most \(\left\lfloor n(n+1)/6\right\rfloor\) pieces, and an absolute additive error at every order. The first-entry argument of [7, Section 8] and the development of Okechukwu [8] are explicit antecedents; the proof here uses IV’s descent. We distinguish transfer from that structural localization and explain why no partition needs to be transported backwards through the descent.

## 1. The partition budget

A clique partition of a finite simple graph \(G\) partitions \(E(G)\) into the edge sets of complete subgraphs of order at least two. Write \(\operatorname{cp}(G)\) for its minimum size and \(c_4(G)\) for the corresponding minimum with all pieces of order at most four. Put

\[
M(n)=\left\lfloor\frac{n(n+1)}6\right\rfloor.
\tag{1.1}
\]

The question of Erdős, Ordman and Zalcstein [1,4] asks for \(\operatorname{cp}(G)\le n^2/6+O(n)\) when \(G\) is chordal. Paper IV [2] proves the stronger eventual bound \(c_4(G)\le M(n)\), with an absolute additive correction for the remaining orders. Here we recover that conclusion through the certificate language of Paper V [3]. The point is to identify the exact interface between structure, physical realization, and the number of partition pieces. The problem has already been resolved in IV and in the two other developments compared there: the preprint signed Anonymous [7] and Okechukwu [8]. Our purpose is expository and organizational. We retain IV's mathematical inputs and their attribution, rather than offering a further independent solution.

For a clique \(Q\) define its gain by

\[
g(Q)=\binom{|Q|}{2}-1.
\]

If a packing \(P\) consists of cliques disjoint in edges, completing all uncovered edges individually gives a partition of size

\[
e(G)-g(P),\qquad g(P)=\sum_{Q\in P}g(Q).
\tag{1.2}
\]

Indeed, each selected clique replaces as many individual edge blocks as it has edges, and contributes one block in their place. Edge-disjointness lets us add these savings without counting an edge twice. No edge outside the selected cliques is changed.

In the mixed model used below, the available pieces are triangles and copies of \(K_4\), with gains two and five. Thus a gain estimate gives an actual partition estimate without a further covering argument. Every output packing in this note consists of cliques of the original graph.

## 2. Transfer with an explicit cost

We use the following form of Paper V's realizable-class transfer, with natural-valued weights and losses. Take a finite collection of weighted auxiliary occurrences, of total weight \(D\), delete occurrences of total weight \(z\), and partition those remaining into \(q\ge1\) classes. For each class \(i\), construct a physical packing \(P_i\) in \(G\) and a nonnegative loss \(r_i\) such that

\[
\text{weight of class }i\le g(P_i)+r_i.
\tag{2.1}
\]

Classes need not be independent in the auxiliary conflict graph. Feasibility is required of their physical realizations. Let \(C=z+\sum_i r_i\). Adding (2.1), some class satisfies

\[
g(P_i)\ge\frac{D-C}{q}.
\tag{2.2}
\]

The remaining classes have total weight \(D-z\). Summing their realization inequalities gives \(\sum_i g(P_i)\ge D-z-\sum_i r_i=D-C\). At least one of the \(q\) gains is at least their average. We choose that one packing; we do not take the union of the packings, which may share edges.

This is the realizable-class transfer theorem [3]. With \(L=D/q\) and \(\rho=C/q\), completion gives

\[
c_4(G)\le e(G)-L+\rho.
\tag{2.3}
\]

**Proposition 2.1.** A certificate with physical triangle/\(K_4\) outputs proves \(c_4(G)\le T\) whenever

\[
qe(G)+C\le qT+D.
\tag{2.4}
\]

**Proof.** Choose the output in (2.2). Its completion has size at most \(e(G)-D/q+C/q\), which is at most \(T\) by (2.4).

There is a useful comparison with the mixed fractional optimum \(W^*(G)\). If \(L\le W^*(G)\), set

\[
\Delta=M(n)-e(G)+W^*(G),\qquad
\gamma=W^*(G)-L.
\]

Equation (2.3) becomes

\[
c_4(G)\le M(n)-\Delta+\gamma+\rho.
\tag{2.5}
\]

To see the cancellation, substitute \(L=W^*(G)-\gamma\) into (2.3), and then use \(e(G)-W^*(G)=M(n)-\Delta\). The two losses are now measured against the same budget: \(\gamma\) is the difference between the fractional optimum and the reference demand per class, whereas \(\rho\) is the realization cost per class.

The sufficient condition is \(\gamma+\rho\le\Delta\). A uniform bound on the integrality gap of every chordal graph is stronger than what this application needs. The certificate only has to fit the margin of the graph under consideration. Neither a small colorability defect nor a cheap realization is supplied merely by writing (2.5).

For the final assembly we use one class. Fix an integer reference \(R\) before constructing the output. If a physical packing \(P\) has \(g(P)\le R\), a single auxiliary demand of weight \(R\) is realized by \(P\) with loss \(R-g(P)\). Its certificate satisfies (2.4) exactly when

\[
e(G)+R-g(P)\le T+R.
\tag{2.6}
\]

The reference \(R\) cancels from the two sides of (2.6). Thus this condition is precisely \(e(G)-g(P)\le T\), the completion cost already identified in (1.2). The hypothesis \(g(P)\le R\) ensures that the recorded loss is nonnegative.

Taking \(R=e(G)\) works for every edge-disjoint packing, because \(g(P)\le e(G)\). This specialization records a previously established physical construction in the transfer interface; it does not improve that construction by averaging. The general \(q\)-class statement remains useful when several realizations are available, but no such improvement is needed for the deduction below.

## 3. The inputs from Paper IV

For precision we state the two combinatorial inputs independently of the final chordal partition theorem. Their proofs belong to Paper IV. Let \(W^*(G)\) be the maximum fractional mixed gain, with capacity one on each edge. Since this is a finite rational linear program, the maximum is attained with a rational primal-dual certificate.

**Input 3.1.** For every \(\zeta>0\) there exists \(N_\zeta\) such that every graph \(G\) of order \(n\ge N_\zeta\) has a physical triangle/\(K_4\) packing \(P\) with

\[
W^*(G)-g(P)\le\zeta n^2.
\tag{3.1}
\]

The formal interface takes a positive rational tolerance. This suffices for the stated real tolerance: choose a positive rational number smaller than \(\zeta\) and apply the interface to that number. The resulting error is also at most \(\zeta n^2\).

Input 3.1 is exactly the case \(r=4\) of Rohatgi–Urschel–Wellens [11, Theorem 3.4]: their integral and fractional objectives give each clique the gain \(\binom{|Q|}{2}-1\), which here is two or five. Their uniform loss is \(o(n^2)\). Haxell–Rödl [9] and Yuster [10, Theorem 1.2] are the transfer antecedents cited there. The formal project of this note uses the proved implementation in Paper IV [2, Theorem 3.1], built from the infrastructure of Paper III; no stronger rounding statement than [11] is claimed for this application. The subquadratic loss suffices in the far regime and is not a linear-error bound. Chordality enters the second input.

**Input 3.2.** There is an absolute \(\eta>0\) such that, for every sufficiently large chordal \(G\) satisfying

\[
e(G)-W^*(G)\ge\frac{n^2}{6}-\eta n^2,
\tag{3.2}
\]

the near-extremal constructor supplies a physical triangle/\(K_4\) packing \(P\) in \(G\) and nonnegative quantities \(m\) and \(A\) with

\[
e(G)-g(P)\le B(n,p)-\frac m{20}-\frac A2,
\qquad
B(n,p)=p(n-p)-\binom p2,
\tag{3.3}
\]

where \(p\) is an integer between zero and \(n\). Here \(m\) and \(A\) are the literal exterior-edge and missing-spoke counts in the retained physical accounts, relative to the regularized root. They are not unspecified errors introduced after the construction.

The concrete formal calibration uses \(\eta=10^{-16}\) and \(n\ge4\cdot10^{12}\) for Input 3.2. We do not optimize these constants. Input 3.1 can require a much larger threshold.

Input 3.2 combines [2, Proposition 4.3, Theorem 5.0 and Lemma 5.3, equation (5.15)]. Its proof has two separate outputs. Vertex-copy descent localizes the original graph near a complete-split comparator. Root regularization and the terminal construction then produce the packing and accounts in (3.3), directly in \(G\). This distinction matters: the descent is used to establish structure, rather than to carry a sequence of partitions back to \(G\).

## 4. The Erdős 81 deduction

We first recall the integer bound on the split baseline. Completing the square gives

\[
B(n,p)=\frac{(2n+1)^2}{24}
-\frac{(6p-2n-1)^2}{24}
\le\frac{n(n+1)}6+\frac1{24}.
\tag{4.1}
\]

Here the first numerator is \(4n(n+1)+1\), which gives the final term \(1/24\). The subtracted square is nonnegative for every integer \(p\); the estimate therefore does not require choosing an extremizing core.

The number \(B(n,p)\) is an integer. The fractional part of \(n(n+1)/6\) is a multiple of \(1/6\), so adding \(1/24\) cannot reach the next integer. Consequently

\[
B(n,p)\le M(n).
\tag{4.2}
\]

**Theorem 4.1.** Assuming Inputs 3.1 and 3.2, there is \(N\) such that every chordal graph \(G\) of order \(n\ge N\) admits a clique partition with all pieces of order at most four and at most \(M(n)\) pieces.

**Proof.** Apply Input 3.1 with \(\zeta=\eta/2\) and take \(N\) large enough for both inputs. Write \(W^*=W^*(G)\). There are two cases. The tolerance is chosen before the graph: a single threshold, the maximum of the two input thresholds, works for every graph considered below.

If \(e(G)-W^*<n^2/6-\eta n^2\), Input 3.1 provides a physical packing \(P\) satisfying

\[
e(G)-g(P)
\le e(G)-W^*+\frac\eta2n^2
<\frac{n^2}{6}-\frac\eta2n^2
\le\frac{n(n+1)}6.
\tag{4.3}
\]

The first inequality adds the rounding loss to the fractional completion cost. The strict far-regime inequality supplies twice the allowed rounding loss, so half of that margin remains. The final comparison only uses \(n\ge0\).

Since \(e(G)-g(P)\) is an integer, it is at most \(M(n)\). The one-class certificate of Section 2, with \(R=e(G)\), therefore satisfies (2.4) for \(T=M(n)\). Proposition 2.1 gives the required partition.

Otherwise (3.2) holds. Input 3.2 supplies a physical packing with

\[
e(G)-g(P)\le B(n,p)-\frac m{20}-\frac A2
\le B(n,p)\le M(n).
\tag{4.4}
\]

The middle inequality drops two nonnegative credits, \(m/20\) and \(A/2\); the last uses the integer baseline bound (4.2). All three estimates refer to the same packing supplied by Input 3.2. The same certificate and Proposition 2.1 finish this case. All selected cliques have order three or four, and completion adds only \(K_2\) pieces.

**Corollary 4.2.** There is an absolute integer \(b\ge0\) such that every chordal graph \(G\) of every order \(n\) satisfies

\[
\operatorname{cp}(G)\le c_4(G)\le M(n)+b
\le\frac{n^2}{6}+\frac n6+b.
\tag{4.5}
\]

**Proof.** Let \(N\) be as in Theorem 4.1 and take \(b=N^2\). For \(n\ge N\) use the theorem. For \(n<N\), the individual edges form a partition with at most \(\binom n2\le N^2\) pieces. The empty graph also satisfies the bound. For \(n\ge1\) the last expression in (4.5) is at most \(n^2/6+(b+1/6)n\); at \(n=0\) no pieces are needed. This is the bound requested in Erdős Problem 81.

The conclusion is already established in Paper IV; this note supplies an explicit transfer assembly from its structural and rounding inputs. It does not prove that \(b=0\) for all orders, nor an improved threshold.

## 5. What transfer replaces

Three questions occur at different points of the argument. Localization asks why a nearly extremal chordal graph has a useful root. Realization asks how auxiliary demands can be converted into cliques of the original graph. Completion asks whether the gain of those cliques pays for the desired number of partition pieces.

The transfer theorem addresses the latter two questions once realizers and their losses have been supplied. It can replace a colorability-based conversion when the classes admit cheaper physical realizations. It does not, by itself, find a root or prove that (3.3) holds. Thus it does not replace the structural role of vertex copying or destabilization in the present deduction.

First entry, used in [7, Section 8] and compared with IV in [2, Section 8], is a localization argument: follow a copying path and identify its first visit to a prescribed neighborhood of the split family. The implementation used for Input 3.2 instead invokes the existing localization-by-descent theorem. That choice avoids a first-entry selector in the selected proof chain. It is a property of the structural input, rather than a consequence of the abstract transfer inequality. Some source modules also contain the alternative first-entry development; importing those modules does not mean that its selector is a premise of the theorem used here.

There is a related benefit of keeping the physical accounts. If every copying step required transporting a partition backwards, losses could accumulate along the path. The route above localizes \(G\) first and constructs its packing once. The loss paid by the transfer certificate is the loss of this final realization. The length of the copying path does not appear as an additional partition cost.

## 6. Place in the series

Papers I and II develop the profile and fractional structural framework; Paper III provides structured packing and rounding infrastructure. Paper IV establishes the localization and physical constructors required here. Paper V isolates the general transfer statement and its realizability cost. The present note makes the interface between the last two papers explicit while retaining attribution of the earlier work.

The note records an alternative organization of part of IV's proof for the release accompanying Paper V. It is not a second, mathematically independent proof of the extremal bound. The budget calculation and separate formal project record precisely how its certificate theorem recovers the established bound from the constructors of IV.

The example also sets a useful limit on the generality of an application claim. Re-encoding a good packing as a one-class certificate establishes compatibility with the engine, but does not demonstrate that the engine supplied new combinatorial savings. A stronger application would construct inexpensive realizers directly from weaker structural information. That remains a separate research direction.

## Formalization and reproducibility

The separate Lean 4.35 project formalizes the physical transfer adapter and the assembly from the proved inputs of IV and V. Its selected dependency audit checks actual use of V's realizable-class transfer and IV's localization by descent, and excludes IV's final global-bound theorem. This exclusion describes the assembly, not mathematical independence from IV. The formal companion identifies the final source freeze, the complete local axiom audit, the public interfaces and reproduction commands. [Sources and formal companion](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/series_notes/NOTE_I_ERDOS81_TRANSFER/05_formalization).

## Acknowledgments

The author is deeply grateful to his wife María Paz and his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support.

## Use of artificial intelligence and computational tools

In the source papers used here, Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check arguments and to prepare the manuscripts. Aristotle, by Harmonic, contributed to exploring approaches, searching for counterexamples, developing proofs, and formalizing and reviewing them in Lean; its role was not limited to translating finished proofs.

For this note, ChatGPT/Codex assisted in assembling the source argument, constructing and checking the Lean adapters, and preparing the exposition and internal audit.

Certo [5] and Jacobian [6] were the computational tools used in the underlying research program to explore instances, check identities, and assess candidates, as disclosed in Paper IV. Their use is acknowledged separately from the logical dependencies of the formal proof. The separate companion and audit records identify the checks performed specifically for this note, including its Python regression checks. Computations were reviewed within their stated scope; a finite search does not replace a universal proof.

The author remains responsible for the arguments, citations, code, and presentation. No AI system is listed as an author.

## References

[1] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” Combinatorics, Probability and Computing 2 (1993), 409–415. <https://doi.org/10.1017/S0963548300000808>.

[2] J. P. Traverso Gianini, Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds, Paper IV, preprint v1.23, October 1, 2026. The version retained in the series distribution is the source for Inputs 3.1 and 3.2. [Manuscript and materials](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/054593443bdece587dda9686a411bb18b0ca34c5/preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_en.md). Deposit: [doi:10.5281/zenodo.23089131](https://doi.org/10.5281/zenodo.23089131).

[3] J. P. Traverso Gianini, Colorability and Realizability Defects in Resource-Dominated Packing Relaxations, Paper V, Preprint 1.0 and accompanying formal source package, October 18, 2026. The realizable-class transfer theorem is the input used in Section 2. [Manuscript and materials](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_V).

[4] T. F. Bloom, “Erdős Problem #81,” Erdős Problems, https://www.erdosproblems.com/81. Cited to identify the problem; this note does not certify the current external review status of proposed solutions.

[5] J. P. Traverso Gianini, *Certo: herramientas computacionales con certificados verificables*. [Manuscript and materials](https://github.com/jtraverso/certo-math).

[6] Morluto and contributors, *Jacobian: herramientas matemáticas componibles*. [Manuscript and materials](https://github.com/morluto/jacobian).


[7] Anonymous, *Clique partitions of chordal graphs with linear error*, preprint, 8 September 2026. Version compared in Paper IV: commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. [Manuscript and materials](https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/manuscript/main.pdf). The manuscript signature is retained. The README at that commit credits Morluto for the mathematical proof and N0zoM1z0 for the manuscript and Lean implementation, with Jacobian at Preference Labs as part of the project; these credits are distinct from the printed authorship.

[8] O. Okechukwu, *Clique partitions and bounded simplicial defect*, arXiv:2609.20871v1, 15 September 2026. <https://arxiv.org/abs/2609.20871v1>. The comparison and scope used here are those documented in Paper IV, Section 8.1.

[9] P. E. Haxell and V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38. <https://doi.org/10.1007/s004930170003>.

[10] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118. <https://doi.org/10.1002/rsa.20048>.

[11] D. Rohatgi, J. C. Urschel, and J. Wellens, “Regarding Two Conjectures on Clique and Biclique Partitions,” *Electronic Journal of Combinatorics* **28**(4) (2021). <https://doi.org/10.37236/9564>. Author version: <https://arxiv.org/abs/2005.02529>.
