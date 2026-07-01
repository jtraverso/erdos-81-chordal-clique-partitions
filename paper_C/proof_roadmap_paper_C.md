# Proof Roadmap — Paper C

## Paper C purpose

Paper C proves the global fractional chordal assembly theorem using the local toolkit from Paper B.

Its core output is:

\[
\boxed{
\text{local fractional packings and debits can be assembled into a global feasible fractional packing.}
}
\]

## Inputs imported

Paper C may import:

From Paper A:

1. chordal/clique-tree setup;
2. nearest-heavy laminar regions;
3. retained cores;
4. branches and corridors;
5. diffuse-region conventions.

From Paper B:

1. Weighted Heavy-Bag Lemma;
2. debit-active boundary group convention;
3. Core-Fan/Farkas allocation theorem;
4. Terminal No-Escape Classification;
5. Boundary-Export \(L_4\) local residue statement;
6. promotion rules.

## Outputs exported to Paper D

Paper C exports a fractional triangle packing theorem of the form:

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

Paper D rounds this to an integral triangle packing statement.

## Main proof chain

### Step 1. Run nearest-heavy recursion

The graph is decomposed into laminar regions.

Regions may be:

1. one-boundary branches;
2. two-boundary corridors;
3. retained cores;
4. terminal diffuse regions;
5. terminal local residues handled by Paper B.

---

### Step 2. Use retained-core ownership

Paper C assigns each edge to a unique active owner.

An edge can be:

1. internal-private;
2. boundary-debit;
3. retained-core;
4. unused.

The ownership map is edge-wise, not subcore-wise.

If a boundary debit loads a core edge \(ij\), that load is charged to the owner of the edge \(ij\), not to an assumed owner of the whole subcore.

This prevents double-loading when retained cores overlap in vertices.

---

### Step 3. Realize active boundary debits

Boundary groups with \(s_\alpha\le1\) are inactive for quadratic core debits.

Active groups have \(s_\alpha\ge2\).

Their debits are allocated into retained-core edge capacity using the Core-Fan/Farkas theorem imported from Paper B.

This includes debits exported by Boundary-Export \(L_4\).

---

### Step 4. Patch local fractional packings

Local packings are feasible because they use only owned edges.

The edge-wise ownership ledger implies:

\[
\text{no edge is loaded by two different active accounts.}
\]

Therefore all local, mixed, boundary-export, core-fan, and retained-core packings patch into one global fractional packing.

---

### Step 5. Quantitative telescoping

Paper C uses the potential:

\[
F(x)=\frac{x^2}{6}.
\]

For each recursive region \(R\), the local amortized inequality has the form:

\[
\operatorname{Loss}(R)
\le
F(m_R)-\sum_jF(m_{R_j})+\operatorname{Err}(R).
\]

Summing over the laminar recursion tree telescopes:

\[
\sum_R
\left(
F(m_R)-\sum_jF(m_{R_j})
\right)
=
F(n)-\sum_{\text{terminal }L}F(m_L)
\le
F(n).
\]

Terminal errors sum to \(o(n^2)\).

Thus:

\[
\operatorname{Loss}(G)
\le
\frac{n^2}{6}+o(n^2).
\]

---

### Step 6. Fractional theorem

The global fractional triangle packing gives:

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

This is the theorem exported to Paper D.

## Reviewer-sensitive wording

Paper C should not claim that the ownership ledger alone proves the quantitative bound.

The ownership ledger proves feasibility:

\[
\text{no double-loading of edges}.
\]

The quantitative bound comes from:

\[
\text{local amortized inequalities}
+
\text{laminar telescoping}.
\]

## What Paper C does not prove

Paper C does not prove the local toolkit. That is Paper B.

Paper C does not prove integral rounding. That is Paper D.

Paper C does not use Paper D.
