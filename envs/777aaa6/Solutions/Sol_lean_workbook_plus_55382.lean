-- Prove2me | solution 1 for lean_workbook_plus_55382
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:22:03.228823+00:00
-- url     : https://prove2.me/submissions/cf26428e-4292-45c8-9a3c-548d877cdf9e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def parameterPolynomial (p u : ℝ) : ℝ :=
  (-4 * p ^ 4 + 16 * p ^ 3 + 16 * p ^ 2) * u ^ 2 +
    (-24 * p ^ 4 + 52 * p ^ 3 + 52 * p ^ 2 + 16) * u +
    4 * p ^ 4 - 32 * p ^ 2 + 64

noncomputable def positiveRemainder (a b : ℝ) : ℝ :=
  24 * a ^ 4 + 412 * a ^ 3 + 2544 * a ^ 2 +
    b * (32 * a ^ 4 + 556 * a ^ 3 + 3456 * a ^ 2 + 8860 * a) +
    b ^ 2 * (4 * a ^ 4 + 64 * a ^ 3 + 344 * a ^ 2 + 640 * a + 100)

theorem shifted_certificate (p u : ℝ) :
    -parameterPolynomial p u - 5520 = 6540 * (p - 5) + 7384 * (u - 1) +
      positiveRemainder (p - 5) (u - 1) := by
  unfold parameterPolynomial positiveRemainder
  ring

theorem remainder_nonnegative (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ positiveRemainder a b := by
  unfold positiveRemainder
  positivity

theorem quantitative_upper_bound (p u : ℝ) (hp : 5 ≤ p) (hu : 1 ≤ u) :
    parameterPolynomial p u ≤ -5520 - 6540 * (p - 5) - 7384 * (u - 1) := by
  have hr := remainder_nonnegative (p - 5) (u - 1) (by linarith) (by linarith)
  have hi := shifted_certificate p u
  linarith

theorem sharp_upper_bound (p u : ℝ) (hp : 5 ≤ p) (hu : 1 ≤ u) :
    parameterPolynomial p u ≤ -5520 := by
  have h := quantitative_upper_bound p u hp hu
  linarith

theorem equality_iff (p u : ℝ) (hp : 5 ≤ p) (hu : 1 ≤ u) :
    parameterPolynomial p u = -5520 ↔ p = 5 ∧ u = 1 := by
  constructor
  · intro he
    have h := quantitative_upper_bound p u hp hu
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    unfold parameterPolynomial
    ring

theorem negative_on_quadrant (p u : ℝ) (hp : 5 ≤ p) (hu : 1 ≤ u) :
    parameterPolynomial p u < 0 := by
  have h := sharp_upper_bound p u hp hu
  linarith

theorem positive_counterfamily (t : ℝ) (ht : 0 ≤ t) :
    0 < 5 + t ∧ 0 < 1 + t ∧ parameterPolynomial (5 + t) (1 + t) < 0 := by
  exact ⟨by linarith, by linarith,
    negative_on_quadrant (5 + t) (1 + t) (by linarith) (by linarith)⟩

theorem solution : ¬ ∀ p u : ℝ,
    (-4 * p ^ 4 + 16 * p ^ 3 + 16 * p ^ 2) * u ^ 2 +
      (-24 * p ^ 4 + 52 * p ^ 3 + 52 * p ^ 2 + 16) * u +
      4 * p ^ 4 - 32 * p ^ 2 + 64 ≥ 0 := by
  intro h
  have hn := negative_on_quadrant 5 1 (by norm_num) (by norm_num)
  have hp := h 5 1
  change 0 ≤ parameterPolynomial 5 1 at hp
  exact (not_lt_of_ge hp) hn
