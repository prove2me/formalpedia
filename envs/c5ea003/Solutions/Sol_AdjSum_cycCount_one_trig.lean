-- Prove2me | solution 1 for AdjSum.cycCount_one_trig
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:35.097388+00:00
-- url     : https://prove2.me/submissions/c27f5035-0b7d-4d82-b75a-0c6dc80ad20d

-- Sol generated from Applications/AdjacentSumPolytopes/Spectral.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence
import Theorems.Thm_AdjSum_cycCount_one

/-!
# A trigonometric form of the two-state spectrum

Numerical experiments (recorded in `ComputationalEvidence.md`) suggest that the
eigenvalues of the adjacent-sum transfer matrix `adjMat s` are exactly

`(-1)^s / (2 cos((2j−1)π/(2s+3)))`,  `j = 1, …, s + 1`.

This file proves the first instance, `s = 1`, completely: the two eigenvalues of
`adjMat 1 = !![1,1;1,0]` are `−1/(2 cos(3π/5)) = φ` and `−1/(2 cos(π/5)) = ψ`, the golden
ratio and its conjugate, and consequently the two-state open and cyclic counts have
*trigonometric* closed forms

`#open(d) = (A^{d+3} − B^{d+3})/√5`,  `#cyclic(d) = A^{d+1} + B^{d+1}`,
`A = −1/(2 cos(3π/5))`, `B = −1/(2 cos(π/5))`.

The dominant pole `A = φ` is the exponential growth rate of both parity classes, an
explicit instance of the abstract growth rate produced in
`Applications.AdjacentSumPolytopes.DominantGrowth`.

-- !-- Lab Notes -- !--
* **Hypothesis.** The transfer matrix is a `0/1` staircase matrix, whose spectrum should
  be a secant family, i.e. reciprocals of cosines at odd multiples of `π/(2s+3)`.
* **Experiment.** Characteristic polynomials computed exactly for `s = 1, …, 7` and
  evaluated at the candidate values `±1/(2 cos((2j−1)π/(2s+3)))`: the residuals are of
  size `10⁻¹⁶`–`10⁻¹⁰` (pure floating-point noise) precisely when the global sign is
  `(-1)^s`, and of size `10⁻¹`–`10⁵` for the other sign.  So the sign alternates with the
  parity of `s`, which is the parity dichotomy of the model showing up spectrally.
* **Analysis.** For `s = 1` the claim is exactly the statement that the golden ratio is
  `−1/(2 cos 3π/5)`, which is provable from `Real.cos_pi_div_five`; the general case
  requires a Chebyshev-type factorisation of `det(xI − adjMat s)` and is recorded as the
  headline conjecture in `FUTURE_DIRECTIONS.md`.
* **Critique.** Nothing here is definitional: the identity `−1/(2 cos 3π/5) = φ` needs
  the exact value of `cos(π/5)`, and the closed forms need Binet's formula together with
  the two Fibonacci identities proved in `Growth.lean`.
-/

open AdjSum

open Real

/-- `cos (3π/5) = (1 − √5)/4`. -/
theorem cos_three_pi_div_five : Real.cos (3 * Real.pi / 5) = (1 - Real.sqrt 5) / 4 := by
  have h : (3 : ℝ) * Real.pi / 5 = Real.pi - 2 * (Real.pi / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

lemma sqrt_five_gt_two : (2 : ℝ) < Real.sqrt 5 := by
  have h : Real.sqrt 4 < Real.sqrt 5 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-- The dominant eigenvalue of the two-state transfer matrix in trigonometric form. -/
theorem trig_eigenvalue_pos :
    -1 / (2 * Real.cos (3 * Real.pi / 5)) = Real.goldenRatio := by
  rw [cos_three_pi_div_five, Real.goldenRatio]
  have h2 := sqrt_five_gt_two
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hne : (1 : ℝ) - Real.sqrt 5 ≠ 0 := by nlinarith
  field_simp
  nlinarith [h5]

/-- The subdominant eigenvalue of the two-state transfer matrix in trigonometric form. -/
theorem trig_eigenvalue_neg :
    -1 / (2 * Real.cos (Real.pi / 5)) = Real.goldenConj := by
  rw [Real.cos_pi_div_five, Real.goldenConj]
  have h2 := sqrt_five_gt_two
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hne : (1 : ℝ) + Real.sqrt 5 ≠ 0 := by nlinarith
  field_simp
  nlinarith [h5]





open AdjSum in
theorem solution(d : ℕ) :
    (cycCount 1 d : ℝ)
      = (-1 / (2 * Real.cos (3 * Real.pi / 5))) ^ (d + 1)
          + (-1 / (2 * Real.cos (Real.pi / 5))) ^ (d + 1) := by
  rw [trig_eigenvalue_pos, trig_eigenvalue_neg, cycCount_one]
  have h5 : Real.sqrt 5 ≠ 0 := by
    have := sqrt_five_gt_two; linarith
  push_cast
  rw [Real.coe_fib_eq, Real.coe_fib_eq, ← Real.goldenRatio_sub_goldenConj]
  have hd : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    rw [Real.goldenRatio_sub_goldenConj]; exact h5
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination (Real.goldenRatio ^ d - Real.goldenConj ^ d) *
      Real.goldenRatio_mul_goldenConj
    + ((Real.goldenConj ^ d - Real.goldenRatio ^ d) / 4) * hsq
