-- Prove2me | solution 1 for AffineScoreTwoKey.abs_tanh_sub_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:06:01.564334+00:00
-- url     : https://prove2.me/submissions/2238d708-3e62-4c5e-a343-77ec2b38f319

-- Sol generated from MachineLearning/TransformerUniversality/AffineScoreTwoKey.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_AffineScoreTwoKey
import Theorems.Thm_AffineScoreTwoKey_abs_tanh_le_abs

/-!
# Affine-score softmax heads: the amplitude–temperature law

`Catalog/MachineLearning/TransformerUniversality/SoftmaxResolution.lean` refuted the conjectured
`Ω(1/N)` resolution barrier for softmax lookup by exhibiting a **two-key** head that
approximates the identity on `[0,1]` to arbitrary accuracy.  The construction used the logit
`log((x+ε)/(1+ε−x))`, an unbounded, task-specific nonlinearity that a real attention layer
cannot produce, and Conjecture 6 of `FUTURE_DIRECTIONS.md` therefore proposed the *affine*
score family as the honest resource class, predicting a `Θ(N^{-2})` error barrier there — in
particular a strictly positive barrier already at `N = 2`.

**This file refutes that conjecture too, and replaces it by a proved conservation law.**

The genuinely affine two-key head, with scores `aᵢx + bᵢ` and values `vᵢ`, computes
`v₂ + (v₁ − v₂)·σ((a₁−a₂)x + (b₁−b₂))` (`twoKeyHead_eq`).  Choosing score scale `a` and values
`1/2 ± 2/a` gives, in closed form, `1/2 + (2/a)·tanh(a(x−1/2)/2)` (`idHead_closed_form`), whose
uniform error against the identity on `[0,1]` is at most `a²/96` (`idHead_error_le`).  So the
affine class has **zero** infimal error (`affine_two_key_eps`), and the conjectured barrier is
false (`no_affine_two_key_barrier`).

What *is* true is a conservation law between the two resources the construction spends.  If any
affine two-key head matches the identity within `ε` at both endpoints of `[0,1]`, then

  `|v₁ − v₂| · |a₁ − a₂| ≥ 4(1 − 2ε)`   (`amplitude_times_scale_ge`),

because the logistic is exactly `1/4`-Lipschitz (`abs_logistic_sub_le`).  The tuned head spends
amplitude `4/a` at score scale `a`, i.e. product exactly `4` (`idHead_amplitude`), so the law is
**sharp**: the construction is optimal, not merely order-optimal
(`amplitude_law_is_sharp`).  Accuracy in the affine class is therefore bought by **amplitude
blow-up**, not by resolution — exactly the resource that a bounded-parameter transformer does
not have.

Analytic groundwork proved here from scratch, since Mathlib's `tanh` API is thin:

* `tanh_eq_exp` — `tanh u = (e^{2u} − 1)/(e^{2u} + 1)`;
* `hasDerivAt_tanh'` — `tanh′ = 1 − tanh²`, hence `abs_tanh_le_abs` (`tanh` is 1-Lipschitz);
* `abs_tanh_sub_le_cube` — the **sharp global cubic bound** `|tanh u − u| ≤ |u|³/3`, by
  monotonicity of `u ↦ u³/3 − (u − tanh u)`, whose derivative `u² − tanh²u` is nonnegative;
* `hasDerivAt_logistic`, `abs_logistic_sub_le` — the logistic is `1/4`-Lipschitz, the optimal
  constant, since `σ′ = e^s/(e^s+1)² ≤ 1/4` by AM–GM.
-/

open scoped BigOperators
open Real

open AffineScoreTwoKey

/-! ## Analytic groundwork: `tanh` and the logistic -/


/-- The derivative of `tanh`. -/
theorem hasDerivAt_tanh' (u : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh u ^ 2) u := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u) hc
  have heq : (Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u) / Real.cosh u ^ 2
      = 1 - Real.tanh u ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  have hfun : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [← heq, hfun]
  exact h







/-! ## The two-key softmax head with affine scores -/



/-! ## The construction: score scale `a`, amplitude `4/a` -/






/-! ## The conservation law: amplitude × score scale -/





open AffineScoreTwoKey in
theorem solution(u : ℝ) : |Real.tanh u - u| ≤ |u| ^ 3 / 3 := by
  set g : ℝ → ℝ := fun t => t ^ 3 / 3 - (t - Real.tanh t) with hg
  have hgd : ∀ t : ℝ, HasDerivAt g (t ^ 2 - Real.tanh t ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).div_const 3
      convert h using 1
      push_cast; ring
    have h2 : HasDerivAt (fun x : ℝ => x - Real.tanh x) (1 - (1 - Real.tanh t ^ 2)) t :=
      (hasDerivAt_id t).sub (hasDerivAt_tanh' t)
    have h := h1.sub h2
    convert h using 1
    ring
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg (fun t => (hgd t).differentiableAt)
    intro t
    rw [(hgd t).deriv]
    have h := abs_tanh_le_abs t
    nlinarith [sq_abs (Real.tanh t), sq_abs t, abs_nonneg (Real.tanh t), abs_nonneg t]
  have hg0 : g 0 = 0 := by simp [hg]
  rcases le_total 0 u with hu | hu
  · have h1 : 0 ≤ g u := by rw [← hg0]; exact hmono hu
    have h2 : Real.tanh u ≤ u := by
      have h := abs_tanh_le_abs u
      rw [abs_of_nonneg hu] at h
      linarith [(abs_le.mp h).2]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg hu]
    simp only [hg] at h1
    linarith
  · have h1 : g u ≤ 0 := by rw [← hg0]; exact hmono hu
    have h2 : u ≤ Real.tanh u := by
      have h := abs_tanh_le_abs u
      rw [abs_of_nonpos hu] at h
      linarith [(abs_le.mp h).1]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos hu]
    simp only [hg] at h1
    linarith
