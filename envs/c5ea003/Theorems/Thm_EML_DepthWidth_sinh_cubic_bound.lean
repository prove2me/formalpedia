-- Prove2me | Theorems.Thm_EML_DepthWidth_sinh_cubic_bound
-- name    : EML.DepthWidth.sinh_cubic_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:44:31.759745+00:00
-- url     : https://prove2.me/theorems/3a60e340-d365-4592-a5c1-cc25360bc82b
-- title:
--   Taylor estimate for `2 sinh`: `|exp u − exp(−u) − 2u| ≤ |u|³/2` for `|u| ≤ 1`.
-- statement:
--   Taylor estimate for `2 sinh`: `|exp u − exp(−u) − 2u| ≤ |u|³/2` for `|u| ≤ 1`.
--
--   ```lean
--   theorem EML.DepthWidth.sinh_cubic_bound(u : ℝ) (hu : |u| ≤ 1) :
--       |Real.exp u - Real.exp (-u) - 2 * u| ≤ |u| ^ 3 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EMLDepthWidthTradeoff.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EMLDepthWidthTradeoff.lean#L275

-- Thm stub generated from Applications/EMLDepthWidthTradeoff.lean
import Mathlib
import Definitions.Def_Applications_EMLDepthWidthTradeoff
/-
# EML expressiveness: depth, width, and a quadratic separation from shallow ReLU

An **EML neuron** computes `x ↦ exp(a x + b) − log(c x + d)` (the activation used
throughout the EML catalog, cf. `eml x y = exp x − log y`).  An **EML layer** of
width `k` is a real affine read-out of `k` such neurons, and depth is obtained by
composing layers.

This file settles, in the univariate model case `f(x) = x²`, the depth/width
trade-off conjectured in the mission statement, and it does so in a *sharper*
form than conjectured.

## Main results

* `sqLayer_eval`, `sqLayer_error` — the **width-2** EML layer
  `S_h(x) = (exp(h x) + exp(−h x) − 2)/h²` (a genuine `Layer 2`, with the
  logarithmic branches switched off by `log 1 = 0`) satisfies
  `|S_h x − x²| ≤ h² x⁴ / 6` whenever `|h x| ≤ 1`.
* `sqLayer_rate` — with `h = 1/n` this is the rate `1/(6 n²)`, a *quadratic*
  improvement on the catalog's forward-difference network
  (`EML.QuadraticApproxRate.emlQuadApprox`, rate `Θ(1/n)`).
* `forward_layer_error_lower_bound` — the forward-difference network really is
  `Θ(h)`: its error at `x = 1` is at least `h/3`.  So the improvement is not an
  artefact of a lossy estimate.
* `sqLayer_error_lower_bound`, `sqLayer_error_two_sided` — the rate is sharp:
  the error at `x = 1` is at least `h²/14`, so the width-2 layer is `Θ(h²)`.
* `sqLayer_deriv_error` — the same fixed-width-2 network approximates the
  *gradient* `2x` to `h²/2` ("smoother gradients").
* `quarticLayer2_error` — the **depth-2** network `S_h ∘ S_h` approximates `x⁴`
  on `[0,1]` with error `≤ h²`; depth composes without losing the rate.
* `relu_shallow_sq_lower_bound` — **lower bound**: *every* one-hidden-layer ReLU
  network with `k` units (even with an affine skip connection and arbitrary real
  parameters) has uniform error at least `1/(32 (k+1)²)` on `x²`.
* `relu_shallow_slope_lower_bound` — the same networks misestimate the *slope*
  `2x` by at least `1/(2(k+1))` somewhere.
* `eml_relu_width_separation` — putting these together: accuracy `ε` costs the
  EML model a *constant* width `2`, while any shallow ReLU model needs
  `(k+1)² ≥ 1/(32 ε)`, i.e. width `Ω(ε^{-1/2})`.

* `prodGate_error_unit`, `prodGate_error_two_sided` — **polarisation**:
  `x y = ((x+y)² − (x−y)²)/4` turns two copies of `S_h` into a width-`4`
  *multiplication gate* whose error on `[0,1]²` is again `Θ(h²)` (at most `h²`,
  at least `2h²/7` at the corner).
* `quadForm_error` — consequently a *single* EML layer of width `4 n²` computes
  every quadratic form on `[0,1]ⁿ` with error `h²·Σ|A i j|`: the constant is
  dimension-free, only the coefficient mass enters.
* `relu_shallow_prod_lower_bound`, `eml_relu_product_separation` — the ReLU
  barrier survives in two inputs: restricting to the diagonal turns a bivariate
  `k`-unit network into a univariate one, so approximating `x y` on `[0,1]²`
  still costs ReLU width `Ω(ε^{-1/2})` while EML pays width `4`.

The converse direction — that depth-2 EML networks *contain* shallow ReLU
networks (via softplus) and therefore also achieve the `O(1/N)` Jackson rate on
the whole Lipschitz class — is proved in the companion file
`Catalog/Applications/EMLSoftplusJackson.lean`.

The ReLU lower bound is proved from scratch: a pigeonhole argument produces a
subinterval of `[0,1]` of length `1/(k+1)` free of breakpoints
(`exists_breakpoint_free_interval`), on which the network is exactly affine
(`reluNet_affine_on_gap`), and an affine function cannot follow a parabola
(`affine_sq_error_lower`).

Everything is self-contained (`import Mathlib` only).
-/

open EML.DepthWidth

open Real Set

noncomputable section

/-! ## 1. EML neurons, layers, and depth -/






/-! ## 2. The width-2 EML layer for `x²` -/







/-! ## 3. The forward-difference layer is genuinely slower -/




/-! ## 3b. Sharpness: the width-2 rate is exactly `Θ(h²)` -/




/-! ## 4. Gradients: the width-2 EML layer also learns the derivative -/

theorem EML.DepthWidth.sinh_cubic_bound(u : ℝ) (hu : |u| ≤ 1) :
    |Real.exp u - Real.exp (-u) - 2 * u| ≤ |u| ^ 3 / 2 := by sorry
