# Calculation Ledger — Paper C

This ledger records the calculations used by Paper C.

## Calculation 1 — Edge-wise ownership

Each edge receives exactly one active owner:

\[
\omega(e)\in
\{\text{internal},\text{boundary},\text{core},\text{unused}\}.
\]

If an edge is inside multiple retained cores, it is owned by the deepest retained core containing both endpoints.

If a boundary debit puts load on \(ij\), the load is charged to \(\omega(ij)\).

This is edge-wise ownership.

No assumption is made that every edge in \(E(S_\alpha)\) has the same retained-core owner.

## Calculation 2 — Private-set disjointness

At a split bag \(b\), child regions are components of the clique tree after removing \(b\).

If a vertex were private in two different children, its connected support would meet two components and therefore contain \(b\). Hence it belongs to the retained core, not to either private set.

Thus sibling private sets are disjoint.

By induction, terminal private interiors are globally disjoint.

## Calculation 3 — No double-loading

Each local account may use only edges owned by that account.

Because \(\omega\) is single-valued:

\[
\sum_{\text{accounts}} \text{load}_a(e)\le 1
\]

for every edge \(e\), after normalization.

Therefore local packings patch into a feasible global fractional packing.

## Calculation 4 — Active boundary debits

A group with

\[
s_\alpha\le1
\]

has no core edge \(ij\subseteq S_\alpha\), so it has no active quadratic debit.

A group with

\[
s_\alpha\ge2
\]

can export or realize a debit through core edges.

Paper B provides the Core-Fan/Farkas allocation.

## Calculation 5 — Boundary-Export \(L_4\) into Paper C

Boundary-Export \(L_4\) produces three types of triangle usage:

\[
b=0:\text{ local internal};
\]

\[
b=1:\text{ local mixed};
\]

\[
b=2:\text{ exported core debit}.
\]

The \(b=2\) component is not paid by the local window. It is sent to the retained-core ledger and realized by Core-Fan/Farkas.

Pure-boundary triangles:

\[
b=3
\]

are not consumed by the local \(L_4\) certificate.

Boundary rank at least three is treated as parent-core involvement.

## Calculation 6 — Local amortized inequality

Each recursive region \(R\) must satisfy:

\[
\operatorname{Loss}(R)
\le
F(m_R)-\sum_jF(m_{R_j})+\operatorname{Err}(R),
\]

where:

\[
F(x)=\frac{x^2}{6}.
\]

This inequality is supplied by the local toolkit of Paper B and the diffuse estimates of Paper A.

Paper C assembles these inequalities; it does not reprove all local cases.

## Calculation 7 — Telescoping

Sum over all internal regions \(R\):

\[
\sum_R\operatorname{Loss}(R)
\le
\sum_R F(m_R)
-
\sum_R\sum_jF(m_{R_j})
+
\sum_R\operatorname{Err}(R).
\]

Every non-root region appears once as a child term and once as a region term.

Therefore all non-root potential terms cancel.

The only uncancelled positive term is:

\[
F(n)=\frac{n^2}{6}.
\]

Thus:

\[
\sum_R\operatorname{Loss}(R)
\le
\frac{n^2}{6}
+
\sum_{\text{terminal }L}\operatorname{Err}(L).
\]

If terminal errors sum to \(o(n^2)\), then:

\[
\sum_R\operatorname{Loss}(R)
\le
\frac{n^2}{6}+o(n^2).
\]

## Calculation 8 — Fractional clique-partition expression

For a fractional triangle packing of weight \(\nu_3^*(G)\), triangle savings produce:

\[
|E(G)|-2\nu_3^*(G).
\]

Paper C proves:

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

## Calculation 9 — Export to Paper D

Paper D uses the standard rounding relation:

\[
\nu_3(G)\ge\nu_3^*(G)-o(n^2).
\]

Then:

\[
|E(G)|-2\nu_3(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2)
\le
\left(\frac16+o(1)\right)n^2.
\]

This is not used inside Paper C.
