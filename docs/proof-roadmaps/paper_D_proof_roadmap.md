# Proof Roadmap — Paper D

## Paper D purpose

Paper D is the final step of the series. It converts the fractional chordal theorem from Paper C into the asymptotic integral clique-partition theorem for chordal graphs.

The main output is:

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

## Inputs imported

Paper D may import:

From Paper A:

1. the split graph lower-bound construction;
2. the fact that split graphs are chordal;
3. the asymptotic lower bound

\[
\operatorname{cp}(K_p\vee\overline K_{2p})
\ge
\frac{n^2}{6}-O(n),
\qquad n=3p.
\]

From Paper C:

1. the fractional chordal theorem

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

From external literature:

1. Haxell--Rödl / Yuster fixed-family fractional-to-integral packing theorem, specialized to triangles:

\[
\nu_3(G)
\ge
\nu_3^*(G)-o(n^2).
\]

## Outputs

Paper D exports the final chordal clique-partition theorem.

It does not export any lemma needed by Papers A, B, or C.

## Main proof chain

### Step 1. Triangle packing saves clique parts

A graph edge partition into singleton edges has \(|E(G)|\) cliques.

Each edge-disjoint triangle replaces three singleton cliques by one triangle clique, saving two parts.

Therefore:

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\]

### Step 2. Round fractional triangles to integral triangles

Use fixed-family fractional-to-integral packing rounding for \(\{K_3\}\):

\[
\nu_3(G)
\ge
\nu_3^*(G)-o(n^2).
\]

Then:

\[
|E(G)|-2\nu_3(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2).
\]

### Step 3. Import Paper C fractional theorem

For chordal graphs:

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

### Step 4. Import Paper A sharpness

The complete split graph

\[
K_p\vee\overline K_{2p},
\qquad n=3p,
\]

is chordal and satisfies:

\[
\operatorname{cp}(K_p\vee\overline K_{2p})
\ge
\frac{n^2}{6}-O(n).
\]

Therefore:

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
\ge
\frac{n^2}{6}-O(n).
\]

### Step 5. Combine upper and lower bounds

Together:

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

## Dependency discipline

Paper D is downstream only.

It may cite Papers A, B, and C, but its actual proof only needs Papers A and C plus the external rounding theorem.

Paper D must not be used as input to Papers A, B, or C.

## Reviewer-sensitive wording

Paper D should not imply that the rounding theorem is new.

It should state clearly that the only new series-specific input is the fractional chordal theorem from Paper C and the sharp split lower bound from Paper A.

## Status

Paper D is a preprint-level final rounding and sharpness step, not a technical draft.
