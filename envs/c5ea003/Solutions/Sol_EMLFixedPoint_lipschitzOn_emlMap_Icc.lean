-- Prove2me | solution 1 for EMLFixedPoint.lipschitzOn_emlMap_Icc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:00:04.352344+00:00
-- url     : https://prove2.me/submissions/b28dc3ae-74e0-42df-be98-a903204e569c

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


/-- Exact derivative of the update on its natural domain. -/
theorem hasDerivAt_emlMap {a c x : ℝ} (hx : x + c ≠ 0) :
    HasDerivAt (emlMap a c) (Real.exp a / (x + c)) x := by
  have h1 : HasDerivAt (fun y => y + c) 1 x := hasDerivAt_id x |>.add_const c
  have h2 : HasDerivAt Real.log ((x + c)⁻¹) (x + c) := Real.hasDerivAt_log hx
  have h3 := h2.comp x h1
  simp at h3
  have h4 := h3.const_mul (Real.exp a)
  convert h4 using 1









open EMLFixedPoint in
theorem solution{a c L U q : ℝ}
    (hpos : 0 < L + c) (hq0 : 0 ≤ q) (hderiv : Real.exp a / (L + c) ≤ q) :
    LipschitzOnWith ⟨q, hq0⟩ (emlMap a c) (Icc L U) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (s := Icc L U)
  · intro x hx
    exact (hasDerivAt_emlMap (by linarith [hx.1] : x + c ≠ 0)).differentiableAt
  · intro x hx
    have hderiv' : HasDerivAt (emlMap a c) (Real.exp a / (x + c)) x := hasDerivAt_emlMap (by linarith [hx.1] : x + c ≠ 0)
    rw [hderiv'.deriv]
    rw [nnnorm_div]
    erw [Real.nnnorm_of_nonneg (Real.exp_nonneg a)]
    erw [Real.nnnorm_of_nonneg (by linarith [hx.1] : x + c ≥ 0)]
    have h1 : Real.exp a / (x + c) ≤ Real.exp a / (L + c) := by
      apply div_le_div_of_nonneg_left (Real.exp_nonneg a) hpos
      linarith [hx.1]
    exact_mod_cast le_trans h1 hderiv
  · exact convex_Icc L U
