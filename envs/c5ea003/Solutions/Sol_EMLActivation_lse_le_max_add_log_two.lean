-- Prove2me | solution 1 for EMLActivation.lse_le_max_add_log_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:56:25.452567+00:00
-- url     : https://prove2.me/submissions/e553e70a-edcc-4ace-a97f-a96d14914072

-- Sol generated from Applications/EML/ActivationMonotonicityTropicalBridge.lean
import Mathlib
import Definitions.Def_Applications_EML_ActivationMonotonicityTropicalBridge

/-!
# EML activation monotonicity and the tropical bridge

An *EML transcendental* is a function built from the exponential and the
logarithm.  This file studies the two-parameter family of **generalized EML
activation functions**

$$ E_{a,b}(x) \;=\; a\,x + \log\bigl(1 + e^{b x}\bigr), $$

which contains the softplus (`a = 0`, `b = 1`), the leaky/residual softplus
(`a > 0`) and, after rescaling, all smoothed rectifiers.

The first half of the file determines the **exact parameter domain** on which
these activations are strictly monotone and strictly convex:

* `emlAct_deriv` : `E_{a,b}'(x) = a + b·σ(bx)` with `σ` the logistic function;
* `emlAct_deriv2` : `E_{a,b}''(x) = b²·σ(bx)(1-σ(bx)) > 0` whenever `b ≠ 0`,
  hence `emlAct_strictConvexOn`: strict convexity for *every* nonzero `b`;
* `emlAct_strictMono_iff` : for `b > 0` the activation is strictly increasing on
  all of `ℝ` **if and only if** `0 ≤ a` — an exact (sharp) parameter bound.

The second half is the **cross-domain bridge**.  The same exponential–logarithm
combination underlies the log-sum-exp operation

$$ x \oplus_b y \;=\; \tfrac1b \log\bigl(e^{bx} + e^{by}\bigr), $$

which is *exactly* (not approximately) associative, commutative, and satisfies
the distributive law `(x+z) ⊕_b (y+z) = (x ⊕_b y) + z`; i.e. `(ℝ, ⊕_b, +)` is,
for each `b ≠ 0`, a semiring-like structure transported from `(ℝ_{>0}, +, ·)` by
the EML isomorphism `x ↦ e^{bx}`.  Letting `b → ∞` this analytic structure
*dequantizes* to the **tropical semiring** (Maslov dequantization):

* `lse_gt_max`, `lse_le_max_add_log_two` : `max x y < x ⊕_b y ≤ max x y + log2/b`;
* `tendsto_lse_max` : `x ⊕_b y → max x y` as `b → ∞`;
* `tendsto_lse_tropical` : the same statement written with Mathlib's `Tropical`
  semiring, `-((-x) ⊕_b (-y)) → untrop (trop x + trop y) = min x y`.

The bridge theorem `eml_activation_tropical_bridge` packages both halves: the
strictly convex, strictly monotone smooth EML activations converge uniformly at
rate `log 2 / b` to the (convex but nowhere strictly convex, merely monotone)
tropical addition `x ↦ max x 0`.  Convex analysis of neural activations and
idempotent (tropical) algebra are thus two ends of one exponential–logarithmic
deformation.
-/

noncomputable section

open Real Filter Topology Set

open EMLActivation

/-! ## The logistic function -/








/-! ## The generalized EML activation -/











/-! ### Exact monotonicity domain -/




/-! ## The log-sum-exp deformation of tropical addition -/


lemma lse_sum_pos (b x y : ℝ) : 0 < Real.exp (b * x) + Real.exp (b * y) := by positivity











/-! ## The bridge theorem -/



open EMLActivation in
theorem solution{b : ℝ} (hb : 0 < b) (x y : ℝ) :
    lse b x y ≤ max x y + Real.log 2 / b := by
  rw [lse, div_le_iff₀ hb]
  have h : Real.exp (b * x) + Real.exp (b * y) ≤ 2 * Real.exp (b * max x y) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      have : Real.exp (b * x) ≤ Real.exp (b * y) := Real.exp_le_exp.2 (by nlinarith)
      linarith
    · rw [max_eq_left h]
      have : Real.exp (b * y) ≤ Real.exp (b * x) := Real.exp_le_exp.2 (by nlinarith)
      linarith
  calc Real.log (Real.exp (b * x) + Real.exp (b * y))
      ≤ Real.log (2 * Real.exp (b * max x y)) := Real.log_le_log (lse_sum_pos b x y) h
    _ = Real.log 2 + b * max x y := by
        rw [Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp]
    _ = (max x y + Real.log 2 / b) * b := by field_simp; ring
