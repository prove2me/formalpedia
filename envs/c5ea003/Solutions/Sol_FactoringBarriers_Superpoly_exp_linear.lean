-- Prove2me | solution 1 for FactoringBarriers.Superpoly_exp_linear
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:35:03.186433+00:00
-- url     : https://prove2.me/submissions/4ed17fd8-ea0d-4caa-b78f-a9d3d8f07d9f

-- Sol generated from Cryptography/FactoringBarriers/AsymptoticLadder.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Theorems.Thm_FactoringBarriers_Superpoly_of_eventually_le
import Theorems.Thm_FactoringBarriers_Superpoly_exp_rpow

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
theorem solution{b : ℝ} (hb : 0 < b) :
    Superpoly (fun x => Real.exp (b * x)) := by
  have h := Superpoly_exp_rpow hb (by norm_num : (0:ℝ) < 1)
  refine h.of_eventually_le ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Real.rpow_one]
