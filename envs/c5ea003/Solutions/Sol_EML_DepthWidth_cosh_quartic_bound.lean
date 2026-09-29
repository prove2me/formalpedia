-- Prove2me | solution 1 for EML.DepthWidth.cosh_quartic_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:43:12.887813+00:00
-- url     : https://prove2.me/submissions/61ad470c-ef2b-44b1-a9ba-8cd205748105

-- Sol generated from Applications/EMLDepthWidthTradeoff.lean
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




/-! ## 5. Depth 2: composing the layer approximates `x⁴` -/


/-! ## 6. Shallow ReLU networks: a matching lower bound -/











/-! ## 7. The separation theorem -/




/-! ## 8. Cycle 3: the EML multiplication gate and multivariate quadratics

The width-2 layer `sqLayer h` squares to second order.  Polarisation
`x y = ((x+y)² − (x−y)²)/4` therefore turns **four** EML neurons into a
*multiplication gate* with the same `O(h²)` accuracy.  Multiplication is the
gateway to several variables: every quadratic form in `n` variables becomes a
single EML layer of width `4 n²`, and — via the diagonal `y = x` — the shallow
ReLU barrier of §7 transfers verbatim to the bivariate target `x y`. -/













/-
-- !-- Lab Notes -- !--

## Hypotheses (Hypothesizer)

H1  (bold) The mission's `O((w·d)^{-2/n})` rate is *not tight* for EML: because
    the activation is entire, a **fixed** width suffices for `x²` and the
    accuracy is bought with weight magnitude, not with width.
H2  The catalog's forward-difference EML network is exactly first order, so the
    published `Θ(1/n)` rate is optimal *for that construction* and the central
    difference strictly beats it.
H3  (bold) Shallow ReLU has a hard `Ω(k^{-2})` barrier on `x²`, so H1 yields a
    genuine model separation, not just a better constant.
H4  (bold) Depth 2 is exactly the depth at which EML contains ReLU: `exp` in the
    first layer and `log` in the second compose into softplus.
H5  Depth composes: `S_h ∘ S_h` still has a second-order rate (target `x⁴`).

## Experiments (Experimenter)

Float sampling of `[0,1]` on a 1001-point grid (details in
`ComputationalEvidence.md`):

  h        max|S_h − x²|   /h²        max|F_h − x²|   /h
  0.5      2.1008e-2       0.084031   1.89770e-1      0.379540
  0.25     5.219e-3        0.083507   8.8813e-2       0.355253
  0.125    1.303e-3        0.083377   4.3002e-2       0.344016
  0.0625   3.26e-4         0.083344   2.1163e-2       0.338607

  h        max|S_h(S_h)−x⁴| /h²       max|S_h′ − 2x|  /h²
  0.5      6.5294e-2        0.261177  8.4381e-2       0.337525
  0.25     1.5795e-2        0.252716  2.0899e-2       0.334377
  0.125    3.917e-3         0.250674  5.212e-3        0.333594

The observed constants `1/12`, `1/3`, `1/4`, `1/3` are all strictly inside the
proved constants `1/6`, `1/3` (matched exactly!), `1`, `1/2`.  H1, H2, H5 pass.

## Analysis (Analyst)

* The `1/12` versus the proved `1/6` gap is *route-dependent*: `Real.exp_bound`
  at `n = 5` costs a factor `1 + 12/50` on the remainder, and we rounded up to a
  provable constant.  "True but the sharp constant needs a different route."
* The forward network's `1/3` is matched *exactly* by
  `forward_layer_error_lower_bound` (from `Real.sum_le_exp_of_nonneg` at `n = 4`),
  so H2 is settled with a sharp constant.
* The ReLU barrier is structural, not analytic: a `k`-unit network is affine on
  one of the `k+1` equal subintervals (pigeonhole on breakpoints), and second
  differences of `x²` cannot be reproduced by an affine map.  The proved
  constant `1/32` versus the optimal `1/8` is the price of evaluating at
  interior quarter points instead of the endpoints of the empty interval.
* H4 turned out to be *more* than a curiosity: since `exp` then `log` gives
  softplus, EML at depth 2 dominates shallow ReLU at equal width, which is what
  transfers the whole Lipschitz theory (`lipschitz_relu_rate`) into EML.

## Critique (Critic)

* No statement is vacuous: every error bound is quantified over an interval with
  non-empty interior, and both lower bounds produce explicit witnesses.
* Hidden assumptions made explicit: `h ≠ 0` (division by `h²`), `|h x| ≤ 1`
  (hypothesis of `Real.exp_bound`), `h ≤ 1/2` in the depth-2 statement (needed so
  that the *output* of the first layer still satisfies `|h y| ≤ 1`).
* The `ReLU` lower bound allows an affine skip connection and arbitrary real
  parameters, so it cannot be dodged by reparametrisation; `w i = 0` units are
  handled separately (they contribute a constant, not a breakpoint).
* Boundary case `k = 0` is included: the pigeonhole argument degenerates to
  "the network is affine on all of `[0,1]`", and the bound reads `ε ≥ 1/32`.
* Caveat on the separation: EML buys accuracy with the read-out weight `1/h²`.
  Under a *bounded-weight* constraint the separation would have to be re-proved;
  this is recorded as Conjecture C1 in `FUTURE_DIRECTIONS.md`.

## Cycle 3 — the multiplication gate (Hypothesize → Experiment → Critique)

H6  (bold) Polarisation makes EML a *multiplicative* model: four neurons compute
    `x y` to second order, so a single EML layer of width `4 n²` realises every
    quadratic form in `n` variables, and the ReLU barrier survives the passage
    to two inputs.

Float sampling of `[0,1]²` on a 51 x 51 grid, gate
`P_h(x,y) = (S_h(x+y) − S_h(x−y))/4`:

  h        max|P_h − x y|   /h²
  0.5      8.6161e-2        0.344645
  0.25     2.1008e-2        0.336124
  0.125    5.219e-3         0.334029
  0.0625   1.303e-3         0.333507

The empirical constant is `1/3`; the proved constant is `17/24 ≈ 0.708`
(`prodGate_error` at `(x,y) = (1,1)`), rounded up to `1` in
`prodGate_error_unit`.  The `2 x` factor between `1/3` and the *worst-case*
polarisation bound is the usual slack of adding `|(x+y)⁴|` and `|(x−y)⁴|`
separately instead of exploiting their opposite signs.  H6 passes.

Cycle 4 closes the rate from below: `prodGate_error_lower_bound` gives
`|P_h(1,1) − 1| ≥ 2h²/7 ≈ 0.2857 h²`, so the true constant `1/3` is now
*bracketed* by proved bounds `2/7 ≤ c ≤ 17/24`, and the gate's rate is `Θ(h²)`
in the strict two-sided sense (`prodGate_error_two_sided`).  Note that the lower
bound needs `h ≤ 1/2`, exactly the hypothesis under which the pre-activation
`h(x+y)` stays in `[−1,1]` — the same constraint as in the upper bound, so the
two-sided statement has no gap in its range of validity.

Critique: the diagonal restriction used in `relu_shallow_prod_lower_bound` is
lossless — a bivariate ReLU unit `relu(w x + v y + b)` restricted to `y = x` is
again a single ReLU unit with weight `w + v` — so the transferred lower bound
`1/(32(k+1)²)` costs nothing and cannot be evaded by choosing `v` adversarially.
The bound is dimension-blind, which is the point: EML's width stays `4` while
ReLU's must grow like `ε^{-1/2}` already in two inputs.

## Synthesis (PI)

For `x²` on `[0,1]`: EML needs width 2 and no depth; shallow ReLU needs
`Ω(ε^{-1/2})` units; the two facts combine into `eml_relu_width_separation`.
For the Lipschitz class, EML at depth 2 matches ReLU's `O(1/N)` exactly, because
depth 2 already contains ReLU up to `log 2 / M`.  The conjectured `O((w d)^{-2})`
rate is therefore correct as an upper bound for smooth targets, but it is *not*
the truth: for analytic targets the correct statement is "constant width,
accuracy governed by weight magnitude".  Cycle 3 upgrades this from a single
target to a *class*: polarisation turns the squaring layer into a multiplication
gate (`prodGate_error_unit`), quadratic forms in `n` variables cost width `4 n²`
with a dimension-free `h²` constant (`quadForm_error`), and the shallow-ReLU
barrier transfers to the bivariate product by diagonal restriction
(`relu_shallow_prod_lower_bound`, `eml_relu_product_separation`).
-/



open EML.DepthWidth in
theorem solution(u : ℝ) (hu : |u| ≤ 1) :
    |Real.exp u + Real.exp (-u) - 2 - u ^ 2| ≤ u ^ 4 / 6 := by
  have h1 := Real.exp_bound hu (n := 5) (by norm_num)
  have h2 := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 5) (by norm_num)
  rw [abs_neg] at h2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  rw [abs_le] at h1 h2 ⊢
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have habs : |u| ^ 5 ≤ u ^ 4 := by
    rw [← h4]
    nlinarith [abs_nonneg u, pow_nonneg (abs_nonneg u) 4]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, habs]
