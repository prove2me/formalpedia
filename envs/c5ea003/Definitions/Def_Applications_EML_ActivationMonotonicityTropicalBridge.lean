-- Prove2me | Definitions.Def_Applications_EML_ActivationMonotonicityTropicalBridge
-- name    : Applications_EML_ActivationMonotonicityTropicalBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:29.88543+00:00
-- url     : https://prove2.me/theorems/a623c677-54a8-4765-90be-c9c8cbac2dfa
-- title:
--   Aether Catalog definitions — Applications_EML_ActivationMonotonicityTropicalBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EML.ActivationMonotonicityTropicalBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EML/ActivationMonotonicityTropicalBridge.lean by skeleton subtraction
import Mathlib

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

namespace EMLActivation

/-! ## The logistic function -/

/-- The logistic (standard sigmoid) function `σ(t) = eᵗ / (1 + eᵗ)`. -/
def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)







/-! ## The generalized EML activation -/

/-- The generalized EML activation `E_{a,b}(x) = a x + log (1 + e^{b x})`. -/
def emlAct (a b x : ℝ) : ℝ := a * x + Real.log (1 + Real.exp (b * x))










/-! ### Exact monotonicity domain -/




/-! ## The log-sum-exp deformation of tropical addition -/

/-- The log-sum-exp ("softmax") operation `x ⊕_b y = (1/b) log (e^{bx} + e^{by})`. -/
def lse (b x y : ℝ) : ℝ := Real.log (Real.exp (b * x) + Real.exp (b * y)) / b












/-! ## The bridge theorem -/


end EMLActivation


