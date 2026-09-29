-- Prove2me | Definitions.Def_Novelty_FloatExpandingShadowing
-- name    : Novelty_FloatExpandingShadowing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:40.349555+00:00
-- url     : https://prove2.me/theorems/9e0f13dc-808b-4837-9baf-f22096403c34
-- title:
--   Aether Catalog definitions — Novelty_FloatExpandingShadowing
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FloatExpandingShadowing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FloatExpandingShadowing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

/-!
# Uniform-in-time shadowing of floating-point executions of expanding polynomials

The finite-time shadowing bound `δ (Lⁿ - 1)/(L - 1)` of
`Novelty.FloatPseudoOrbitShadowing` degrades exponentially with the number of
steps.  This file proves that the degradation is an artifact of *forward*
tracking: for an **expanding** map the pseudo-orbit produced by a floating-point
execution is shadowed by a genuine orbit with an error bound
`δ / (λ - 1)` that is **uniform in the number of steps** — the classical
hyperbolic shadowing mechanism, made effective and combined with the
backward-error semantics of the arithmetic.

* `expanding_backward_shadowing` — the abstract theorem, proved by constructing
  the shadowing orbit backwards along inverse branches (a `1/λ`-contraction).
* `cubicExpand` / `cubic_inverse` — the concrete expanding polynomial map
  `p(z) = z³ + 2z`, whose global inverse branch is `1/2`-Lipschitz.
* `cubic_fl_shadowed_uniformly` — the composed theorem: any finite binary64
  execution of `p` staying within magnitude `B` is shadowed, uniformly in the
  number of steps, by an exact real orbit of `p`, with error at most
  `γ₈(u) (2B + B³)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the exponential factor in the previous cycle's
logistic bound is not intrinsic to floating-point chaos; it is the price of
insisting that the shadowing orbit start at the *same* point.  Allowing the
initial condition to move should give an `O(u)` bound uniform in time.
Experiment (Experimenter): formalize backward construction along inverse
branches.  The induction is on the horizon `N`, shifting both the pseudo-orbit
and the branch family; the resulting error satisfies
`e_n ≤ (δ + e_{n+1})/λ`, whose fixed point is `δ/(λ-1)`.
Analysis (Analyst): the certificate consumed is exactly the one produced by the
semantics layer, confirming the modularity claim: no property of the arithmetic
beyond the local defect bound is used.
Critique (Critic): expansivity is essential — the logistic map at r = 4 has a
critical point and admits no globally `1/λ`-Lipschitz inverse branch, so the
theorem does not silently subsume the previous cycle's result.  The concrete
instantiation uses a genuinely expanding cubic, for which surjectivity (hence
existence of the branch) is proved from the intermediate-value theorem.
-- !-- End Lab Notes -- !--
-/

namespace Novelty.FloatBackwardError

open scoped BigOperators


/-! ### A concrete expanding polynomial dynamical system -/

/-- The expanding cubic `p(z) = z³ + 2z`. -/
def cubicExpand (z : ℝ) : ℝ := z ^ 3 + 2 * z

/-- Coefficient list of `p` for Horner evaluation. -/
def cubicCoeffs : List ℝ := [0, 2, 0, 1]




lemma cubicExpand_surjective : Function.Surjective cubicExpand := by
  have hcont : Continuous cubicExpand := by
    unfold cubicExpand; fun_prop
  refine hcont.surjective ?_ ?_
  · refine Filter.tendsto_atTop_mono' _ ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with z hz
    have : 0 ≤ z ^ 3 := by positivity
    simp only [id, cubicExpand]; linarith
  · refine Filter.tendsto_atBot_mono' _ ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_le_atBot (0:ℝ)] with z hz
    have : z ^ 3 ≤ 0 := by nlinarith [sq_nonneg z]
    simp only [id, cubicExpand]; linarith

/-- The (global) inverse branch of the expanding cubic. -/
noncomputable def cubicInv : ℝ → ℝ := Function.surjInv cubicExpand_surjective





end Novelty.FloatBackwardError


