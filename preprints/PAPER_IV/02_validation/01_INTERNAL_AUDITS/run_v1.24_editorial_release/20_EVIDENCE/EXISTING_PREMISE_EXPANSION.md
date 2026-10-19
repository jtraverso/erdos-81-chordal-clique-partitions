# Existing premise expanded in Appendix F.5

Source: frozen `E34/L11Params.lean`, lines 289–292.

SHA-256 of source file: `227d217ebf46750f164b539f664d2f421d6cb881edfa141b5f383cd1d8336475`.

```lean
theorem thm2_ineq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K : ℕ} (hK : 1 ≤ K) :
    2 * (1 - δ11 ε K / 4) ^ m11V ε K *
      (1 + m11V ε K * 2 ^ K / (1 - δ11 ε K / 4)) ^ B11 ε K ≤ 1 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
```

Only its already-referenced conclusion is printed in the new manuscript. The assumptions are supplied in the preceding paragraph. No source was changed and no new proof was added.
