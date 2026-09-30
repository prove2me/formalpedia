-- Prove2me | solution 1 for lean_workbook_plus_59684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:27:36.007039+00:00
-- url     : https://prove2.me/submissions/6617e16e-7944-4b06-84ce-8346f7330b79

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

def orderedShiftedGap (a b c : ℝ) : ℝ :=
  (a + b + 2) * (b + c + 4) * (c + a + 6) - 8 * (a + 1) * (b + 2) * (c + 3)

theorem ordered_shifted_gap_refinement (a b c : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    16 * (b - a) + 4 * (c - b) ≤ orderedShiftedGap a b c := by
  let u := b - a
  let v := c - b
  have hu : 0 ≤ u := sub_nonneg.mpr hab
  have hv : 0 ≤ v := sub_nonneg.mpr hbc
  have h : orderedShiftedGap a b c =
      2 * a * (u ^ 2 + u * v + 4 * u + v ^ 2 + 2 * v) +
      u * (2 * u ^ 2 + 3 * u * v + 12 * u + v ^ 2 + 8 * v) +
      2 * v ^ 2 + 16 * u + 4 * v := by
    dsimp [orderedShiftedGap, u, v]
    ring
  have hp : 0 ≤ 2 * a * (u ^ 2 + u * v + 4 * u + v ^ 2 + 2 * v) +
      u * (2 * u ^ 2 + 3 * u * v + 12 * u + v ^ 2 + 8 * v) + 2 * v ^ 2 := by
    positivity
  change 16 * u + 4 * v ≤ orderedShiftedGap a b c
  linarith only [h, hp]

theorem ordered_shifted_gap_zero_iff (a b c : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    orderedShiftedGap a b c = 0 ↔ a = b ∧ b = c := by
  constructor
  · intro h
    have := ordered_shifted_gap_refinement a b c ha hab hbc
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    unfold orderedShiftedGap
    ring

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) :
    (a + b + 2) * (b + c + 4) * (c + a + 6) ≥ 8 * (a + 1) * (b + 2) * (c + 3) := by
  have h := ordered_shifted_gap_refinement a b c ha hb hc
  unfold orderedShiftedGap at h
  linarith

#print axioms solution
#print axioms ordered_shifted_gap_refinement
#print axioms ordered_shifted_gap_zero_iff
