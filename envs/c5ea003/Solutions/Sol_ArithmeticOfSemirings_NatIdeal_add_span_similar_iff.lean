-- Prove2me | solution 1 for ArithmeticOfSemirings.NatIdeal.add_span_similar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:26:52.525586+00:00
-- url     : https://prove2.me/submissions/b1abb59d-2253-4e99-be92-acb807094269

import Mathlib
import Definitions.Def_Tropical_ArithmeticOfSemiringsIdeals
open ArithmeticOfSemirings in
theorem solution (A : Ideal ℕ) (r : ℕ) :
    NatIdeal.Similar (A + Ideal.span {r}) A ↔ NatIdeal.IsIntegralOver A r := by
  constructor
  · -- from `(A + (r))·C = A·C`, the witness `C` already integrates `r`
    rintro ⟨C, hC, hEq⟩
    refine ⟨C, hC, ?_⟩
    calc Ideal.span {r} * C ≤ (A + Ideal.span {r}) * C := by
          gcongr
          simp
      _ = A * C := hEq
  · -- conversely `(r)·B ≤ A·B` collapses the sum
    rintro ⟨B, hB, hle⟩
    refine ⟨B, hB, ?_⟩
    rw [add_mul, Ideal.add_eq_sup]
    exact le_antisymm (sup_le le_rfl hle) le_sup_left
