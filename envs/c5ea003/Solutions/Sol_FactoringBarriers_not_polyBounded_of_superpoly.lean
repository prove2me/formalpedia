-- Prove2me | solution 1 for FactoringBarriers.not_polyBounded_of_superpoly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:17.350661+00:00
-- url     : https://prove2.me/submissions/d87126fe-8985-4d18-bbbf-fcf11c440fc1

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
theorem solution{f : ℝ → ℝ} (hf : Superpoly f) :
    ¬ PolyBounded f := by
  rintro ⟨C, d, hCd⟩
  have hdiv : Tendsto (fun x => f x / x ^ d) atTop atTop := hf d
  have hbdd : ∀ᶠ x : ℝ in atTop, f x / x ^ d ≤ C := by
    filter_upwards [hCd, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 d)]
    linarith [hx]
  have := (hdiv.eventually (eventually_gt_atTop C)).and hbdd
  rcases this.exists with ⟨x, h1, h2⟩
  linarith
