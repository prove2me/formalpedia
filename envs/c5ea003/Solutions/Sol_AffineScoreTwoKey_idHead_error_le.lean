-- Prove2me | solution 1 for AffineScoreTwoKey.idHead_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:08:49.804092+00:00
-- url     : https://prove2.me/submissions/f801c902-adc5-454c-bef6-87300c8f0425

-- Sol generated from MachineLearning/TransformerUniversality/AffineScoreTwoKey.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_AffineScoreTwoKey
import Theorems.Thm_AffineScoreTwoKey_abs_tanh_sub_le_cube

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

/-- `tanh` in exponential form. -/
theorem tanh_eq_exp (u : ℝ) : Real.tanh u = (Real.exp (2 * u) - 1) / (Real.exp (2 * u) + 1) := by
  have h1 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have hu : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have h2 : Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, h1, h2]
  field_simp





theorem logistic_eq_tanh (s : ℝ) : logistic s = 1 / 2 + Real.tanh (s / 2) / 2 := by
  have h : Real.tanh (s / 2) = (Real.exp s - 1) / (Real.exp s + 1) := by
    have h2 : 2 * (s / 2) = s := by ring
    rw [tanh_eq_exp, h2]
  have hpos : (0 : ℝ) < Real.exp s + 1 := by positivity
  rw [logistic, h]
  field_simp
  ring



/-! ## The two-key softmax head with affine scores -/


/-- **Reduction to the logit gap.**  Only the difference of the two affine scores matters. -/
theorem twoKeyHead_eq (a₁ b₁ a₂ b₂ v₁ v₂ x : ℝ) :
    twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ x
      = v₂ + (v₁ - v₂) * logistic ((a₁ - a₂) * x + (b₁ - b₂)) := by
  have hA : (0 : ℝ) < Real.exp (a₁ * x + b₁) := Real.exp_pos _
  have hB : (0 : ℝ) < Real.exp (a₂ * x + b₂) := Real.exp_pos _
  have hexp : Real.exp ((a₁ - a₂) * x + (b₁ - b₂))
      = Real.exp (a₁ * x + b₁) / Real.exp (a₂ * x + b₂) := by
    rw [← Real.exp_sub]
    ring_nf
  rw [twoKeyHead, logistic, hexp]
  field_simp
  ring

/-! ## The construction: score scale `a`, amplitude `4/a` -/


/-- **Closed form** of the tuned head. -/
theorem idHead_closed_form {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    idHead a x = 1 / 2 + (2 / a) * Real.tanh (a * (x - 1 / 2) / 2) := by
  rw [idHead, twoKeyHead_eq, logistic_eq_tanh]
  have harg : (a - 0) * x + (-a / 2 - 0) = a * (x - 1 / 2) := by ring
  rw [harg]
  field_simp
  ring




/-! ## The conservation law: amplitude × score scale -/





open AffineScoreTwoKey in
theorem solution{a x : ℝ} (ha : 0 < a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |idHead a x - x| ≤ a ^ 2 / 96 := by
  set u : ℝ := a * (x - 1 / 2) / 2 with hu
  have habs : |u| ≤ a / 4 := by
    rw [hu, abs_div, abs_mul, abs_of_pos ha, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      div_le_div_iff₀ (by norm_num) (by norm_num)]
    have hhalf : |x - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (x - 1 / 2), ha.le]
  have hbound := abs_tanh_sub_le_cube u
  have hxu : x = 1 / 2 + (2 / a) * u := by field_simp [hu]; ring
  have hdiff : idHead a x - x = (2 / a) * (Real.tanh u - u) := by
    rw [idHead_closed_form ha.ne' x, ← hu, hxu]; ring
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / a)]
  have hcube : |u| ^ 3 ≤ (a / 4) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) habs 3
  calc (2 / a) * |Real.tanh u - u| ≤ (2 / a) * (|u| ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (2 / a) * ((a / 4) ^ 3 / 3) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = a ^ 2 / 96 := by field_simp; ring
