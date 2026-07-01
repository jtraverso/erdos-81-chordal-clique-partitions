# Calculation Ledger — Paper D

This ledger records the calculations used by Paper D.

## Calculation 1 — Triangle packing to clique partition

Start with \(|E(G)|\) singleton-edge cliques.

For every edge-disjoint triangle, replace three singleton cliques by one triangle clique.

Each triangle saves:

\[
3-1=2
\]

cliques.

For a maximum edge-disjoint triangle packing of size \(\nu_3(G)\):

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\]

## Calculation 2 — Fractional-to-integral rounding

The fixed-family rounding theorem gives, for triangles:

\[
\nu_3(G)
\ge
\nu_3^*(G)-o(n^2).
\]

Multiply by \(-2\):

\[
-2\nu_3(G)
\le
-2\nu_3^*(G)+o(n^2).
\]

Therefore:

\[
|E(G)|-2\nu_3(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2).
\]

## Calculation 3 — Insert Paper C

Paper C proves:

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

Thus:

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

## Calculation 4 — Split graph lower bound

Paper A supplies the split graph construction:

\[
G_p=K_p\vee\overline K_{2p},
\qquad n=3p.
\]

It is chordal because every split graph is chordal.

Paper A proves:

\[
\operatorname{cp}(G_p)
\ge
\frac{n^2}{6}-O(n).
\]

Therefore:

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
\ge
\frac{n^2}{6}-O(n).
\]

## Calculation 5 — Final asymptotic equality

Upper bound:

\[
\max\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

Lower bound:

\[
\max\operatorname{cp}(G)
\ge
\frac{n^2}{6}-O(n).
\]

Since:

\[
O(n)=o(n^2),
\]

we get:

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

## Calculation 6 — No backward dependency

Paper D uses Paper C but Paper C does not use Paper D.

The rounding step is downstream:

\[
\text{fractional theorem}
\Rightarrow
\text{integral theorem}.
\]

It never feeds back into the local or fractional proof.
