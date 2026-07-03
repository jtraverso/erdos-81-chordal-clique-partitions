import Mathlib
/-!
# The Envelope Lemma (algebraic core)
This file formalizes the purely algebraic heart of the *Envelope Lemma* (Lemma 2) of
the paper *Clique Partitions of Split Graphs and the 1/6 Barrier*.
After the normalization `a = s/µ`, `c = r/µ`, `u = Z(R)/µ²` used in the proof, the
Envelope Lemma reduces to the following real inequalities on the closed triangle
`{a ≥ 1, c ≥ 0, a + c ≤ 3}`:
* `envelope_ineqI` :  `a·(a-1)·(3-a) + (2-a)·c² ≥ 0`   (governs the case `c ≤ a`);
* `envelope_ineqM` :  `M(a,c) := -3a² - 2ac + 12a - c² + 6c - 9 ≥ 0`  (case `c > a`);
and the final pointwise inequality (`envelope_pointwise`)
  `a/2 + u + max (c(a-1)/2) (ac/2 - (a/c)·u) ≥ (a+c)²/4 - (a+c)/2 + 3/4`
valid for every admissible slack `u ∈ [c²/6, c/2]`.  The `max` here is exactly the
expression `u + max{A, B(u)}` minimized in the paper; proving the bound pointwise for
all admissible `u` is equivalent to (and slightly stronger than) bounding the minimum.
-/
namespace ErdosSplit
/-
Case `c ≤ a` inequality: the difference between the intersection value and the
envelope, cleared of denominators, is `a(a-1)(3-a) + (2-a)c² ≥ 0`.
-/
theorem envelope_ineqI (a c : ℝ) (ha : 1 ≤ a) (hc : 0 ≤ c) (hac : a + c ≤ 3) :
    0 ≤ a * (a - 1) * (3 - a) + (2 - a) * c ^ 2 := by
  by_cases ha2 : a ≤ 2;
  · exact add_nonneg ( mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by linarith ) ) ( mul_nonneg ( by linarith ) ( sq_nonneg _ ) );
  · nlinarith [ sq_nonneg ( a - 3 / 2 ), mul_le_mul_of_nonneg_left ( le_of_not_ge ha2 ) hc ]
/-
Case `c > a` inequality: the difference `M(a,c) := -3a² - 2ac + 12a - c² + 6c - 9`
is nonnegative on the triangle `{a ≥ 1, c ≥ 0, a + c ≤ 3}`.
-/
theorem envelope_ineqM (a c : ℝ) (ha : 1 ≤ a) (hc : 0 ≤ c) (hac : a + c ≤ 3) :
    0 ≤ -3 * a ^ 2 - 2 * a * c + 12 * a - c ^ 2 + 6 * c - 9 := by
  nlinarith [ sq_nonneg ( a - 1 ), sq_nonneg ( c - 1 ), mul_le_mul_of_nonneg_right ha ( sub_nonneg.2 hac ) ]
/-
The Envelope Lemma inequality, pointwise in the slack variable `u`.
For `a ≥ 1`, `c > 0`, `a + c ≤ 3`, and any `u` with `c²/6 ≤ u ≤ c/2`,
the left-hand side of the packing bound dominates the target envelope.
-/
theorem envelope_pointwise (a c u : ℝ) (ha : 1 ≤ a) (hc : 0 < c) (hac : a + c ≤ 3)
    (hulo : c ^ 2 / 6 ≤ u) (huhi : u ≤ c / 2) :
    (a + c) ^ 2 / 4 - (a + c) / 2 + 3 / 4 ≤
      a / 2 + u + max (c * (a - 1) / 2) (a * c / 2 - (a / c) * u) := by
  cases max_cases ( c * ( a - 1 ) / 2 ) ( a * c / 2 - a / c * u );
  · field_simp at *;
    nlinarith [ mul_le_mul_of_nonneg_left ha hc.le, mul_le_mul_of_nonneg_left hac hc.le, envelope_ineqI a c ha hc.le hac ];
  · cases le_or_gt 1 c <;> nlinarith [ mul_div_cancel₀ a ( ne_of_gt hc ) ]
end ErdosSplit
