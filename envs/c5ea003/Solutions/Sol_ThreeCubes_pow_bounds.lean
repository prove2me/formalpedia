-- Prove2me | solution 1 for ThreeCubes.pow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:25:30.623192+00:00
-- url     : https://prove2.me/submissions/3f9432f3-4553-49c1-91ca-64ef4ee97c4a

-- Sol generated from Probability/Counting.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Counting

/-!
# Counting representations: `1` and `2` are exceptional

Heath-Brown's conjecture predicts that for a *generic* admissible `n` the number of
representations `n = x³ + y³ + z³` with `max(|x|,|y|,|z|) ≤ B` grows like `c_n log B`.  The
integers `1` and `2` are famously exceptional: the classical one-parameter families give
`≫ B^{1/4}` and `≫ B^{1/3}` representations respectively, which is vastly more than
logarithmic.

This file makes those lower bounds explicit and formal:

* `ThreeCubes.card_repsBox_one` : at least `2T+1` representations of `1` inside the box of
  radius `12T⁴ + 9T³ + 3T + 1`, i.e. `≫ B^{1/4}` representations of height `≤ B`;
* `ThreeCubes.card_repsBox_two` : at least `2T+1` representations of `2` inside the box of
  radius `6T³ + 6T² + 1`, i.e. `≫ B^{1/3}` representations of height `≤ B`.
-/

open ThreeCubes








open ThreeCubes in
theorem solution{t T : ℤ} (h : |t| ≤ T) :
    t ^ 4 ≤ T ^ 4 ∧ t ^ 3 ≤ T ^ 3 ∧ -T ^ 3 ≤ t ^ 3 ∧ t ^ 2 ≤ T ^ 2 ∧ t ≤ T ∧ -T ≤ t := by
  have habs := abs_nonneg t
  have h4 : |t| ^ 4 ≤ T ^ 4 := pow_le_pow_left₀ habs h 4
  have h3 : |t| ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ habs h 3
  have h2 : |t| ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ habs h 2
  have e4 : t ^ 4 = |t| ^ 4 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  have e2 : t ^ 2 = |t| ^ 2 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  have e3 : |t ^ 3| = |t| ^ 3 := abs_pow t 3
  have hle := abs_le.mp h
  refine ⟨by omega, ?_, ?_, by omega, hle.2, hle.1⟩
  · have : t ^ 3 ≤ |t ^ 3| := le_abs_self _
    omega
  · have : -|t ^ 3| ≤ t ^ 3 := neg_abs_le _
    omega
