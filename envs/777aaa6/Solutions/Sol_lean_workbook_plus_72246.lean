-- Prove2me | solution 1 for lean_workbook_plus_72246
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:22:32.712282+00:00
-- url     : https://prove2.me/submissions/7e5b0fe2-164e-4d3b-8a7a-4653940af36d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem nonlinear_product_bound_and_equality (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : a + b ≤ 2) :
    (a + 1) * (a * b ^ 2 + 1) ≤ 4 ∧
      ((a + 1) * (a * b ^ 2 + 1) = 4 ↔ a = 1 ∧ b = 1) := by
  have ha2 : 0 ≤ 2 - a := by linarith
  have hab2 : 0 ≤ 2 - a - b := by linarith
  have hab' : 0 ≤ 2 - a + b := by linarith
  have hq : 0 < 3 + a - a ^ 2 := by
    have := mul_nonneg ha2 (show 0 ≤ a + 1 by linarith)
    nlinarith
  have hfirst : 0 ≤ (1 - a) ^ 2 * (3 + a - a ^ 2) := mul_nonneg (sq_nonneg _) hq.le
  have hsecond : 0 ≤ a * (a + 1) * (2 - a - b) * (2 - a + b) := by positivity
  have hidentity : 4 - (a + 1) * (a * b ^ 2 + 1) =
      (1 - a) ^ 2 * (3 + a - a ^ 2) +
        a * (a + 1) * (2 - a - b) * (2 - a + b) := by ring
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hsquare : (1 - a) ^ 2 = 0 := by nlinarith [sq_nonneg (1 - a)]
    have ha1 : a = 1 := by nlinarith
    have hfactor : (b - 1) * (b + 1) = 0 := by rw [ha1] at he; nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · exact ⟨ha1, by linarith⟩
    · linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0)
    (hab : (a + 1) * (a * b ^ 2 + 1) ≥ 4) : a + b ≥ 2 := by
  by_contra h
  have hs : a + b < 2 := lt_of_not_ge h
  obtain ⟨hle, heq⟩ := nonlinear_product_bound_and_equality a b ha hb hs.le
  obtain ⟨ha1, hb1⟩ := heq.mp (le_antisymm hle hab)
  linarith

#print axioms solution
#print axioms nonlinear_product_bound_and_equality
