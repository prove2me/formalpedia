-- Prove2me | solution 1 for lean_workbook_plus_65807
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:17.742959+00:00
-- url     : https://prove2.me/submissions/a1b58908-601d-4c81-bc23-418428f0c746

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable def mixed_quartic (a b c : ℝ) : ℝ :=
  a ^ 4 / 4 + a ^ 3 * b / 4 + a ^ 3 * c / 4 + a ^ 2 * b * c / 4 +
    a * b ^ 3 / 4 + a * b ^ 2 * c / 4 + a * b * c ^ 2 / 4 + a * c ^ 3 / 4 +
      b ^ 4 / 4 + b ^ 3 * c / 4 + b * c ^ 3 / 4 + c ^ 4 / 4

theorem mixed_quartic_factorization (a b c : ℝ) :
    mixed_quartic a b c = (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) / 4 := by
  unfold mixed_quartic
  ring

theorem mixed_quartic_counterfamily (t : ℝ) :
    mixed_quartic (2 * t) (2 * t) (-3 * t) = -(23 / 4) * t ^ 4 := by
  unfold mixed_quartic
  ring

theorem mixed_quartic_counterfamily_negative (t : ℝ) (ht : t ≠ 0) :
    mixed_quartic (2 * t) (2 * t) (-3 * t) < 0 := by
  rw [mixed_quartic_counterfamily]
  have hp : 0 < t ^ 4 := by
    nlinarith [sq_pos_of_ne_zero (pow_ne_zero 2 ht)]
  nlinarith

theorem mixed_quartic_nonnegative_inputs (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ mixed_quartic a b c := by
  rw [mixed_quartic_factorization]
  positivity

theorem solution : ¬ (∀ a b c : ℝ,
    a ^ 4 / 4 + a ^ 3 * b / 4 + a ^ 3 * c / 4 + a ^ 2 * b * c / 4 +
      a * b ^ 3 / 4 + a * b ^ 2 * c / 4 + a * b * c ^ 2 / 4 + a * c ^ 3 / 4 +
        b ^ 4 / 4 + b ^ 3 * c / 4 + b * c ^ 3 / 4 + c ^ 4 / 4 ≥ 0) := by
  intro h
  have he := h 2 2 (-3)
  change 0 ≤ mixed_quartic 2 2 (-3) at he
  have hn := mixed_quartic_counterfamily_negative 1 one_ne_zero
  simp only [mul_one] at hn
  exact (not_le_of_gt hn) he

#print axioms solution
#print axioms mixed_quartic_counterfamily_negative
#print axioms mixed_quartic_nonnegative_inputs
