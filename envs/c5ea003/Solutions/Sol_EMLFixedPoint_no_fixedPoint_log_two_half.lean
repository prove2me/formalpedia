-- Prove2me | solution 1 for EMLFixedPoint.no_fixedPoint_log_two_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:14.95454+00:00
-- url     : https://prove2.me/submissions/ce59a131-01d0-4e93-a471-c589b3aa33ab

-- Sol generated from Applications/EML/FixedPointIteration.lean
import Mathlib
import Definitions.Def_Applications_EML_FixedPointIteration

/-!
# Fixed points of an exponential--logarithmic iteration

This file studies `x ↦ exp a * log (x + c)`.  The unrestricted test claim from
this research question is false: even with `0 < a < 1` and `0 < c < 1`, a fixed
point need not exist.  We prove this for `a = log 2`, `c = 1/2` on the natural
logarithmic domain.

The positive result is the precise contraction theorem suggested by the question.
On a closed invariant interval `[L,U]`, if `L+c>0` and
`exp a / (L+c) ≤ q < 1`, the map has a unique fixed point in the interval;
every iteration starting there converges to it with Banach's geometric error bound.
-/

noncomputable section

open Real Set Filter Function Topology

open EMLFixedPoint











open EMLFixedPoint in
theorem solution{x : ℝ} (hdomain : 0 < x + (1 / 2 : ℝ)) :
    emlMap (Real.log 2) (1 / 2) x ≠ x := by
  unfold emlMap
  rw [Real.exp_log (by norm_num : (2 : ℝ) > 0)]
  intro heq
  -- heq : 2 * log (x + 1/2) = x
  have hexp : x + 1/2 = Real.exp (x/2) := by
    have h1 : log (x + 1/2) = x/2 := by linarith
    rw [← h1, Real.exp_log hdomain]
  -- Let y = x/2, so exp(y) = 2y + 1/2
  set y := x / 2 with hy_def
  have hexp_y : Real.exp y = 2 * y + 1/2 := by
    have : x = 2 * y := by ring
    linarith
  -- Key lemma: exp(y) ≥ 2y + 2(1 - log 2) for all y (tangent line at y = log 2)
  have htangent : ∀ z : ℝ, Real.exp z ≥ 2 * z + 2 * (1 - Real.log 2) := by
    intro z
    -- exp(z) = 2 * exp(z - log 2) ≥ 2 * (1 + (z - log 2)) = 2z + 2 - 2*log 2
    have h := Real.add_one_le_exp (z - Real.log 2)
    calc Real.exp z = Real.exp (z - Real.log 2 + Real.log 2) := by ring_nf
      _ = Real.exp (z - Real.log 2) * Real.exp (Real.log 2) := by rw [Real.exp_add]
      _ = Real.exp (z - Real.log 2) * 2 := by rw [Real.exp_log (by norm_num : (2 : ℝ) > 0)]
      _ ≥ (1 + (z - Real.log 2)) * 2 := by nlinarith
      _ = 2 * z + 2 - 2 * Real.log 2 := by ring
      _ = 2 * z + 2 * (1 - Real.log 2) := by ring
  -- Now 2(1 - log 2) > 1/2 since log 2 < 3/4
  have h_bound : 2 * (1 - Real.log 2) > 1/2 := by
    have : Real.log 2 < 3/4 := Real.log_two_lt_d9.trans_le (by norm_num : (0.6931471808 : ℝ) ≤ 3/4)
    linarith
  have hcontra : Real.exp y > 2 * y + 1/2 := by linarith [htangent y]
  linarith
