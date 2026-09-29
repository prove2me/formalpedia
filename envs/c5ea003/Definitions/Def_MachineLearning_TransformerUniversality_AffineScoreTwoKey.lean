-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_AffineScoreTwoKey
-- name    : MachineLearning_TransformerUniversality_AffineScoreTwoKey
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:23.139731+00:00
-- url     : https://prove2.me/theorems/c3dd869c-079f-4a44-8014-b5509d5cd444
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_AffineScoreTwoKey
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.AffineScoreTwoKey`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/AffineScoreTwoKey.lean by skeleton subtraction
import Mathlib

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

namespace AffineScoreTwoKey

/-! ## Analytic groundwork: `tanh` and the logistic -/





/-- The logistic (two-key softmax) function. -/
noncomputable def logistic (s : ℝ) : ℝ := Real.exp s / (Real.exp s + 1)




/-! ## The two-key softmax head with affine scores -/

/-- A two-key softmax head with **affine** scores `aᵢ x + bᵢ` and values `vᵢ`. -/
noncomputable def twoKeyHead (a₁ b₁ a₂ b₂ v₁ v₂ x : ℝ) : ℝ :=
  (v₁ * Real.exp (a₁ * x + b₁) + v₂ * Real.exp (a₂ * x + b₂)) /
    (Real.exp (a₁ * x + b₁) + Real.exp (a₂ * x + b₂))


/-! ## The construction: score scale `a`, amplitude `4/a` -/

/-- The affine two-key head tuned to the identity at score scale `a`: scores `a x − a/2` and
`0`, values `1/2 ± 2/a`. -/
noncomputable def idHead (a x : ℝ) : ℝ :=
  twoKeyHead a (-a / 2) 0 0 (1 / 2 + 2 / a) (1 / 2 - 2 / a) x





/-! ## The conservation law: amplitude × score scale -/




end AffineScoreTwoKey


