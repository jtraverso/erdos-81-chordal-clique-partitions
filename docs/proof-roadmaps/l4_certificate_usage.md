# \(L_4\) Certificate Usage

## What the \(L_4\) certificate is not

The \(L_4\) certificate is not an unrestricted window-sweep theorem.

It does not claim:

\[
\text{every interacting span-four interval system is locally }L_4\text{-decomposable}.
\]

That stronger statement is not needed.

## What the \(L_4\) certificate is

The \(L_4\) certificate is a finite exact validation of the final local residue after structural reduction.

The structural reduction is:

\[
\text{good-tail removal}
+
\text{bounded-multiplicity ear absorption}
+
\text{overload promotion}
+
\text{boundary-rank reduction}.
\]

Only after this reduction is the \(L_4\) local certificate invoked.

## Boundary-export version

Let \(B\) be the set of boundary types in a local \(L_4\) residue.

Boundary rank is:

\[
\rho(B)=|B|.
\]

The certificate covers:

\[
\rho(B)\le2.
\]

The eleven \(L_4\) types give:

\[
\binom{11}{0}+\binom{11}{1}+\binom{11}{2}=67
\]

boundary interfaces.

Each interface is checked exactly.

## Triangle classification

Every triangle is classified by the number \(b\) of boundary vertices.

### \(b=0\)

Internal local triangle.

It consumes only local internal edge atoms.

### \(b=1\)

Mixed local triangle.

It consumes local-local and boundary-local atoms. These are part of the local interface account.

### \(b=2\)

Exported core debit.

The triangle contains two boundary vertices and one local vertex.

Its boundary-boundary edge is not paid locally. It is exported to the parent retained-core ledger.

### \(b=3\)

Pure parent-core triangle.

This is forbidden in the local certificate. If pure-boundary capacity is needed, the problem is no longer a local \(L_4\) residue.

## Boundary rank at least three

If:

\[
\rho(B)\ge3,
\]

the residue is treated as parent-core involvement.

The allowed outcomes are:

1. common-core/sunflower promotion;
2. long-core/five-window promotion;
3. explicit global parent-core allocation;
4. lower-order residue below threshold.

It is not certified as a local \(L_4\) problem.

## Required repository package

The repository should include:

```text
certificates/l4_boundary_export/
  README.md
  l4_types.json
  l4_edge_atoms.json
  l4_triangle_atoms.json
  boundary_sets_rank_le_2.json
  l4_boundary_export_certificates.json
  verify_l4_boundary_export.py
  verifier_output.txt
```

## Verifier requirements

For every boundary set \(B\) with \(|B|\le2\), the verifier should check:

1. equations are exact rational equations;
2. all triangle weights are nonnegative;
3. no forbidden pure-boundary triangle is used;
4. \(b=0\) and \(b=1\) loads remain local;
5. \(b=2\) loads are exported as core debits;
6. exported debit format is compatible with Core-Fan/Farkas;
7. total residual error is within the permitted lower-order ledger.

## Recommended paper wording

Use:

> The \(L_4\) certificate is included as a finite exact validation of the boundary-export local residue after structural reduction. It is not used as an unrestricted window-sweep theorem.

Do not use:

> The \(L_4\) certificate proves all span-four window sweeps.

## Status

With the boundary-export certificate package attached, the \(L_4\) component is a finite machine-checkable local certificate, not an informal computational assumption.
