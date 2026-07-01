# Proof Roadmap - Paper D

## Role in the series

Paper D is the final assembly note converting the fractional chordal theorem into the integral clique-partition theorem.

It depends on:

```text
Paper A: lower bound / sharpness
Paper C: fractional chordal theorem
Haxell-Rodl / Yuster: fractional-to-integral triangle-packing rounding
```

It does not reprove the recursive chordal analysis from Paper C.

## Main theorem

For chordal graphs on n vertices,

```text
max cp(G) = (1/6 + o(1)) n^2.
```

## Proof structure

1. Start from the clique-partition inequality:

```text
cp(G) <= |E(G)| - 2 nu_3(G).
```

2. Use fractional-to-integral rounding:

```text
nu_3(G) >= nu_3^*(G) - o(n^2).
```

3. Import the Paper C fractional chordal theorem:

```text
|E(G)| - 2 nu_3^*(G) <= (1/6 + o(1)) n^2.
```

4. Combine the inequalities to get the chordal upper bound.

5. Import the split construction from Paper A for sharpness.

## Scope

Paper D is intentionally short. Its job is to assemble previously proved ingredients and keep the dependency chain explicit.

