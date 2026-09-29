-- Prove2me | solution 1 for FactoringBarriers.Lfun_superpoly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:35:02.615671+00:00
-- url     : https://prove2.me/submissions/9aef369b-df82-4d48-b83e-6c65accb7bc3

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

/-- For `x ≥ e` and `α ≤ 1` we have `L[α,c] x ≥ exp (c x^α)`. -/
theorem exp_rpow_le_Lfun {α c x : ℝ} (hc : 0 ≤ c) (hα : α ≤ 1) (hx : Real.exp 1 ≤ x) :
    Real.exp (c * x ^ α) ≤ Lfun α c x := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog : (1:ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    simpa using this
  have hpow : (1:ℝ) ≤ (Real.log x) ^ (1 - α) :=
    Real.one_le_rpow hlog (by linarith)
  have hxa : (0:ℝ) ≤ x ^ α := (Real.rpow_pos_of_pos hx0 α).le
  have : c * x ^ α ≤ c * x ^ α * (Real.log x) ^ (1 - α) := by
    nlinarith [mul_nonneg hc hxa]
  exact Real.exp_le_exp.mpr this


/-! ## The `L`-functions are subexponential -/



/-! ## Superpolynomial lower bounds exclude polynomial time -/



/-! ## Separation of the rungs -/




open FactoringBarriers in
theorem solution{α c : ℝ} (hc : 0 < c) (hα : 0 < α) (hα1 : α ≤ 1) :
    Superpoly (Lfun α c) := by
  refine (Superpoly_exp_rpow hc hα).of_eventually_le ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  exact exp_rpow_le_Lfun hc.le hα1 hx
