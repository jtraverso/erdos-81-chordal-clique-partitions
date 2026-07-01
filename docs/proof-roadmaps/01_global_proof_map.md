# Global Proof Map

## Goal

The chordal branch aims to prove the asymptotic clique-partition upper bound through a modular proof chain:

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2
\]

for the relevant chordal configuration class, via fractional triangle packing and final rounding.

## High-level chain

### Paper A — Structural setup

Expected role:

1. define the chordal/clique-tree language;
2. define regions, branches, corridors, retained cores, and nearest-heavy recursion;
3. prove the laminar decomposition framework;
4. prove basic diffuse estimates;
5. provide the structural objects imported by Paper B.

Paper A should not cite Paper B, C, or D.

---

### Paper B — Local chordal toolkit

Main role:

\[
\text{local terminal region}
\Rightarrow
\text{reduction, absorption, promotion, or local certificate}.
\]

Paper B proves or packages:

1. Weighted Heavy-Bag Lemma;
2. Core-Fan/Farkas capacity allocation;
3. single-ear budget;
4. bounded-multiplicity simplicial sweep;
5. overload extraction;
6. boundary-export \(L_4\) local certificate usage;
7. terminal no-escape classification.

Paper B may cite Paper A.

---

### Paper C — Fractional chordal assembly

Main role:

\[
\text{local toolkit}
+
\text{ownership ledger}
+
\text{telescoping}
\Rightarrow
\text{global fractional packing}.
\]

Paper C proves:

1. edge-wise retained-core ownership;
2. no double-loading of edges;
3. boundary debit realization through Core-Fan/Farkas;
4. conditional quantitative telescoping;
5. global fractional chordal theorem.

Paper C may cite Paper A and Paper B.

---

### Paper D — Integral rounding

Main role:

\[
\nu_3(G)
\ge
\nu_3^*(G)-o(n^2).
\]

Then:

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2).
\]

Paper D may cite Paper A, Paper B, and Paper C, plus the standard Haxell–Rödl/Yuster rounding theorem.

## Critical non-circularity

Paper B proves local tools without using Paper C.

Paper C assembles local tools without modifying them.

Paper D only rounds the fractional theorem; it does not feed back into Papers B or C.

## Role of \(L_4\)

The \(L_4\) certificate is not a universal span-four window-sweep theorem.

Its role is:

\[
\text{after good-tail, ear-budget, overload promotion, and boundary-rank reduction,}
\]

verify the finite remaining boundary-export local residue.

Boundary rank \(\le2\) is certified/exported.

Boundary rank \(\ge3\) is treated as parent-core involvement and is promoted or globally allocated.
