-- Prove2me | solution 1 for FactoringBarriers.exp_linear_not_subexp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:15.834768+00:00
-- url     : https://prove2.me/submissions/518a9eae-bff2-454f-a811-a956b3aa3bd5

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
theorem solution{b : ℝ} (hb : 0 < b) :
    ¬ Subexp (fun x => Real.exp (b * x)) := by
  intro h
  have h2 := h (b / 2) (by linarith)
  have hgrow : Tendsto (fun x : ℝ => Real.exp (b * x) / Real.exp (b / 2 * x)) atTop atTop := by
    have : ∀ x : ℝ, Real.exp (b * x) / Real.exp (b / 2 * x) = Real.exp ((b / 2) * x) := by
      intro x; rw [← Real.exp_sub]; ring_nf
    simp only [this]
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < b / 2) tendsto_id)
  have := (hgrow.eventually (eventually_gt_atTop (1:ℝ))).and
    (h2.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)))
  rcases this.exists with ⟨x, hx1, hx2⟩
  linarith
