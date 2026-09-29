-- Prove2me | solution 1 for FactoringBarriers.Lfun_subexp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:33:23.708913+00:00
-- url     : https://prove2.me/submissions/6b2ed1dc-fbf4-49fe-a65f-b3d748760419

-- Sol generated from Cryptography/FactoringBarriers/AsymptoticLadder.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Theorems.Thm_FactoringBarriers_tendsto_rpow_mul_log_rpow_div_atTop

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
theorem solution{α c : ℝ} (hc : 0 < c) (hα1 : α < 1) :
    Subexp (Lfun α c) := by
  intro ε hε
  have key : ∀ᶠ x : ℝ in atTop,
      Lfun α c x / Real.exp (ε * x) ≤ Real.exp (-(ε / 2) * x) := by
    have hsmall : ∀ᶠ x : ℝ in atTop,
        x ^ α * (Real.log x) ^ (1 - α) / x < ε / (2 * c) := by
      have h0 : (0:ℝ) < ε / (2 * c) := by positivity
      exact ((tendsto_rpow_mul_log_rpow_div_atTop hα1).eventually
        (eventually_lt_nhds h0)) |>.mono (fun x hx => hx)
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx1
    have hlt := (div_lt_iff₀ hx0).mp hx
    have hkey : c * x ^ α * (Real.log x) ^ (1 - α) < (ε / 2) * x := by
      have h2 : c * (x ^ α * (Real.log x) ^ (1 - α)) < c * (ε / (2 * c) * x) :=
        mul_lt_mul_of_pos_left hlt hc
      have h3 : c * (ε / (2 * c) * x) = ε / 2 * x := by
        field_simp
      calc c * x ^ α * (Real.log x) ^ (1 - α)
          = c * (x ^ α * (Real.log x) ^ (1 - α)) := by ring
        _ < c * (ε / (2 * c) * x) := h2
        _ = ε / 2 * x := h3
    rw [Lfun, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hlim : Tendsto (fun x : ℝ => Real.exp (-(ε / 2) * x)) atTop (𝓝 0) := by
    have hpos : Tendsto (fun x : ℝ => Real.exp ((ε / 2) * x)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < ε / 2) tendsto_id)
    refine hpos.inv_tendsto_atTop.congr (fun x => ?_)
    simp only [Pi.inv_apply, ← Real.exp_neg]
    ring_nf
  refine squeeze_zero' ?_ key hlim
  filter_upwards with x
  simp only [Lfun]
  positivity
