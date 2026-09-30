-- Prove2me | solution 1 for lean_workbook_plus_73621
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:29.837844+00:00
-- url     : https://prove2.me/submissions/c74999a3-5840-44b7-b9b6-52b47f765189

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (k : ℕ) :
    (∃ x : ℕ, x ^ 2 = k) ↔ (∃ x : ℕ, (x : ℝ) = Real.sqrt k) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg x)]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hs : (x : ℝ) ^ 2 = (k : ℝ) := by
      rw [hx, Real.sq_sqrt (Nat.cast_nonneg k)]
    exact_mod_cast hs

#print axioms solution
