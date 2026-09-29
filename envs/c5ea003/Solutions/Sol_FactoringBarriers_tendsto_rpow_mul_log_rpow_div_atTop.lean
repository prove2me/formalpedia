-- Prove2me | solution 1 for FactoringBarriers.tendsto_rpow_mul_log_rpow_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:31:18.772702+00:00
-- url     : https://prove2.me/submissions/a41bce76-469d-4fea-8b04-894d21c093c2

-- Sol generated from Cryptography/FactoringBarriers/AsymptoticLadder.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder

/-!
# The Asymptotic Ladder for Classical Factoring Barriers

This file develops the *quantitative* backbone of the conditional-impossibility
framework for classical integer factoring.  Every known classical factoring
resource comes with a running-time barrier, and each barrier is expressed in
terms of the bit-size parameter `x = log N`.

The three shapes that occur are

* `x ↦ exp (b * x)` (exponential; e.g. `N^{1/4}` for Pollard rho, `b = 1/4`);
* `Lfun α c x = exp (c * x^α * (log x)^(1-α))` (subexponential `L_N[α, c]`;
  e.g. `L_N[1/3,c]` for the number field sieve, `L_p[1/2,√2]` for ECM);
* `x ↦ C * x^d` (polynomial — the target of a hypothetical fast algorithm).

Main results:

* `Superpoly_exp_rpow`  : `exp (c * x^α)` is superpolynomial for `c, α > 0`;
* `Lfun_superpoly`      : `L[α,c]` is superpolynomial for `0 < α ≤ 1`, `c > 0`;
* `Lfun_subexp`         : `L[α,c]` is *sub*exponential for `0 < α < 1`;
* `not_polyBounded_of_superpoly` : a superpolynomial lower bound rules out
  polynomially bounded running time.

Together these say that the `L`-functions occupy a genuine intermediate rung of
the ladder: strictly above every polynomial and strictly below every exponential.
-/

open FactoringBarriers

open Filter Real
open scoped Topology

/-! ## Growth classes -/





/-! ## Superpolynomiality is inherited by domination -/


/-! ## The basic exponential rung -/



/-! ## The `L`-functions are superpolynomial -/



/-! ## The `L`-functions are subexponential -/



/-! ## Superpolynomial lower bounds exclude polynomial time -/



/-! ## Separation of the rungs -/




open FactoringBarriers in
theorem solution{α : ℝ} (hα1 : α < 1) :
    Tendsto (fun x : ℝ => x ^ α * (Real.log x) ^ (1 - α) / x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (one_ne_zero)
    simpa using this
  have hcont : ContinuousAt (fun t : ℝ => t ^ (1 - α)) 0 :=
    Real.continuousAt_rpow_const 0 (1 - α) (Or.inr (by linarith))
  have hz : ((0:ℝ) ^ (1 - α)) = 0 := Real.zero_rpow (by linarith)
  have hcomp : Tendsto (fun x : ℝ => (Real.log x / x) ^ (1 - α)) atTop (𝓝 0) := by
    have := (hcont.tendsto.comp hlog)
    rw [hz] at this
    exact this
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  have hlx : (0:ℝ) < Real.log x := Real.log_pos hx
  have hxa : (0:ℝ) < x ^ (1 - α) := Real.rpow_pos_of_pos hx0 _
  have hsum : x ^ α * x ^ (1 - α) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  rw [Real.div_rpow hlx.le hx0.le, div_eq_div_iff hxa.ne' hx0.ne']
  calc Real.log x ^ (1 - α) * x
      = Real.log x ^ (1 - α) * (x ^ α * x ^ (1 - α)) := by rw [hsum]
    _ = x ^ α * Real.log x ^ (1 - α) * x ^ (1 - α) := by ring
