-- Prove2me | solution 1 for exp_le_quad
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:18:21.310674+00:00
-- url     : https://prove2.me/submissions/c584c73e-2e65-4396-baed-fa6073d9aeed

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem solution (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x^2 := by
  set phi : ℝ → ℝ := fun t => Real.exp (-t) * (1 + t + t^2) with hphi
  have hderiv : ∀ t : ℝ, HasDerivAt phi (Real.exp (-t) * (t * (1 - t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      have := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => 1 + t + t^2) (1 + 2*t) t := by
      have ha : HasDerivAt (fun t : ℝ => (1:ℝ) + t) 1 t := by simpa using (hasDerivAt_id t).const_add 1
      have hb : HasDerivAt (fun t : ℝ => t^2) (2*t) t := by simpa using hasDerivAt_pow 2 t
      have h := ha.add hb
      convert h using 1
    have := h1.mul h2
    convert this using 1
    ring
  have hphi0 : phi 0 = 1 := by simp [hphi]
  have hge : 1 ≤ phi x := by
    rcases lt_or_ge x 0 with hx0 | hx0
    · -- x < 0 : phi antitone on Iic 0, so phi x ≥ phi 0
      have hanti : AntitoneOn phi (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Iic] at ht
          have ht0 : t < 0 := ht
          have hneg : t * (1 - t) ≤ 0 := by nlinarith [ht0]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          nlinarith [mul_nonneg hexp.le (neg_nonneg.mpr hneg)]
      have := hanti (Set.mem_Iic.mpr (le_of_lt hx0)) (Set.mem_Iic.mpr le_rfl) (le_of_lt hx0)
      rwa [hphi0] at this
    · -- 0 ≤ x : phi monotone on Icc 0 1, so phi x ≥ phi 0
      have hmono : MonotoneOn phi (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Icc] at ht
          have ht0 : 0 < t := ht.1
          have ht1 : t < 1 := ht.2
          have hge0 : 0 ≤ t * (1 - t) := by nlinarith [ht0, ht1]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          positivity
      have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩) (Set.mem_Icc.mpr ⟨hx0, hx⟩) hx0
      rwa [hphi0] at this
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hge' : 1 ≤ Real.exp (-x) * (1 + x + x^2) := hge
  rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ hexp] at hge'
  linarith [hge']
