-- Prove2me | solution 1 for FactoringBarriers.Superpoly_exp_rpow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:33:24.225445+00:00
-- url     : https://prove2.me/submissions/f1233a95-6b11-4399-b63b-c7ae29689d21

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
theorem solution{c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    Superpoly (fun x => Real.exp (c * x ^ α)) := by
  intro d
  have hcomp :
      Tendsto (fun x : ℝ => Real.exp (c * x) / x ^ (d / α)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (d / α) c hc
  have hrp : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα
  refine (hcomp.comp hrp).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxd : (x ^ α) ^ (d / α) = x ^ d := by
    rw [← Real.rpow_mul hx.le, mul_div_cancel₀ d hα.ne']
  simp [hxd]
