-- Prove2me | solution 1 for AffineScoreTwoKey.amplitude_times_scale_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:06:02.233298+00:00
-- url     : https://prove2.me/submissions/a2b1ed79-dff1-47ea-9d94-6c6fe077c4c7

-- Sol generated from MachineLearning/TransformerUniversality/AffineScoreTwoKey.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_AffineScoreTwoKey

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







theorem hasDerivAt_logistic (s : ℝ) :
    HasDerivAt logistic (Real.exp s / (Real.exp s + 1) ^ 2) s := by
  have hE : (0 : ℝ) < Real.exp s + 1 := by positivity
  have h1 : HasDerivAt (fun t => Real.exp t) (Real.exp s) s := Real.hasDerivAt_exp s
  have h2 : HasDerivAt (fun t => Real.exp t + 1) (Real.exp s) s := h1.add_const 1
  have h := h1.div h2 hE.ne'
  convert h using 1
  field_simp
  ring

/-- **The logistic is `1/4`-Lipschitz**, with the optimal constant: `σ′ = e^s/(e^s+1)² ≤ 1/4`
by AM–GM, with equality at `s = 0`. -/
theorem abs_logistic_sub_le (p q : ℝ) : |logistic p - logistic q| ≤ |p - q| / 4 := by
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖Real.exp x / (Real.exp x + 1) ^ 2‖ ≤ 1 / 4 := by
    intro x _
    have hE : (0 : ℝ) < Real.exp x := Real.exp_pos x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.exp x - 1)]
  have := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_logistic x).hasDerivWithinAt) hb (Set.mem_univ q) (Set.mem_univ p)
  simpa [Real.norm_eq_abs, div_eq_inv_mul, mul_comm] using this

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






/-! ## The conservation law: amplitude × score scale -/





open AffineScoreTwoKey in
theorem solution{a₁ b₁ a₂ b₂ v₁ v₂ eps : ℝ}
    (h0 : |twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 0 - 0| ≤ eps)
    (h1 : |twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 1 - 1| ≤ eps) :
    4 * (1 - 2 * eps) ≤ |v₁ - v₂| * |a₁ - a₂| := by
  have e0 : twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 0 = v₂ + (v₁ - v₂) * logistic (b₁ - b₂) := by
    rw [twoKeyHead_eq]; ring_nf
  have e1 : twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 1
      = v₂ + (v₁ - v₂) * logistic ((a₁ - a₂) + (b₁ - b₂)) := by
    rw [twoKeyHead_eq]; ring_nf
  have hgap : 1 - 2 * eps ≤ |twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 1 - twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 0| := by
    have hA := abs_le.mp h0
    have hB := abs_le.mp h1
    rcases le_total (twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 1) (twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 0) with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith [hA.1, hA.2, hB.1, hB.2]
    · rw [abs_of_nonneg (by linarith)]; linarith [hA.1, hA.2, hB.1, hB.2]
  have hdiff : twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 1 - twoKeyHead a₁ b₁ a₂ b₂ v₁ v₂ 0
      = (v₁ - v₂) * (logistic ((a₁ - a₂) + (b₁ - b₂)) - logistic (b₁ - b₂)) := by
    rw [e0, e1]; ring
  rw [hdiff, abs_mul] at hgap
  have hlip : |logistic ((a₁ - a₂) + (b₁ - b₂)) - logistic (b₁ - b₂)| ≤ |a₁ - a₂| / 4 := by
    have h := abs_logistic_sub_le ((a₁ - a₂) + (b₁ - b₂)) (b₁ - b₂)
    have harg : ((a₁ - a₂) + (b₁ - b₂)) - (b₁ - b₂) = a₁ - a₂ := by ring
    rwa [harg] at h
  have hmono : |v₁ - v₂| * |logistic ((a₁ - a₂) + (b₁ - b₂)) - logistic (b₁ - b₂)|
      ≤ |v₁ - v₂| * (|a₁ - a₂| / 4) := mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
  linarith
