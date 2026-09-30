-- Prove2me | solution 1 for lean_workbook_plus_38119
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:07:57.324012+00:00
-- url     : https://prove2.me/submissions/80233401-df95-493b-8e4a-0fdc25c8f506

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable def three_zero_quartic (a b : ℝ) : ℝ :=
  a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) * (a + b) ^ 2 + 3 - 6 * a * b * (a + b)

theorem three_zero_quartic_decomposition (a b : ℝ) :
    2 * three_zero_quartic a b = 2 * ((a - 1) * (b - 1)) ^ 2 +
      ((a + b - 2) * (a + b + 1)) ^ 2 + ((a - b) * (a + b + 1)) ^ 2 := by
  unfold three_zero_quartic
  ring

theorem solution (a b : ℝ) :
    a ^ 2 * b ^ 2 + (a ^ 2 + b ^ 2) * (a + b) ^ 2 + 3 -
      6 * a * b * (a + b) ≥ 0 := by
  change 0 ≤ three_zero_quartic a b
  linarith [three_zero_quartic_decomposition a b,
    sq_nonneg ((a - 1) * (b - 1)), sq_nonneg ((a + b - 2) * (a + b + 1)),
    sq_nonneg ((a - b) * (a + b + 1))]

theorem three_zero_quartic_equality (a b : ℝ) :
    three_zero_quartic a b = 0 ↔
      (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = -2) ∨ (a = -2 ∧ b = 1) := by
  constructor
  · intro he
    have h1 := sq_nonneg ((a - 1) * (b - 1))
    have h2 := sq_nonneg ((a + b - 2) * (a + b + 1))
    have h3 := sq_nonneg ((a - b) * (a + b + 1))
    have hz1 : ((a - 1) * (b - 1)) ^ 2 = 0 := by
      linarith [three_zero_quartic_decomposition a b]
    have hz2 : ((a + b - 2) * (a + b + 1)) ^ 2 = 0 := by
      linarith [three_zero_quartic_decomposition a b]
    have hu := mul_eq_zero.mp (sq_eq_zero_iff.mp hz1)
    have hv := mul_eq_zero.mp (sq_eq_zero_iff.mp hz2)
    rcases hu with ha | hb
    · rcases hv with hp | hp
      · left
        constructor <;> linarith
      · right; left
        constructor <;> linarith
    · rcases hv with hp | hp
      · left
        constructor <;> linarith
      · right; right
        constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      unfold three_zero_quartic <;> ring

#print axioms solution
#print axioms three_zero_quartic_equality
