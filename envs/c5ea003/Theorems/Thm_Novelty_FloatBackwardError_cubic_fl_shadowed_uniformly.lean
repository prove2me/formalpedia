-- Prove2me | Theorems.Thm_Novelty_FloatBackwardError_cubic_fl_shadowed_uniformly
-- name    : Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:13:53.721079+00:00
-- url     : https://prove2.me/theorems/78e415a3-ed06-41d0-aa4a-97c3286ba142
-- title:
--   **Composed theorem: uniform-in-time certified shadowing of a floating-point
-- statement:
--   **Composed theorem: uniform-in-time certified shadowing of a floating-point
--   execution of an expanding polynomial.**
--
--   Any finite floating-point execution of `p(z) = z³ + 2z` (Horner evaluation, any
--   IEEE-754 arithmetic with unit roundoff `u`, no overflow or exceptional values)
--   that is observed to stay within magnitude `B` is shadowed by an *exact* real
--   orbit of `p`, with error at most `γ₈(u) (2B + B³)` at **every** step — a bound
--   independent of the number of steps executed.
--
--   ```lean
--   theorem Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly(M : RoundingModel) (x₀ B : ℝ) (N : ℕ)
--       (hB : ∀ n ≤ N, |flOrbit M cubicCoeffs x₀ n| ≤ B) :
--       ∃ y : ℕ → ℝ, (∀ n < N, cubicExpand (y n) = y (n + 1)) ∧
--         (∀ n ≤ N, |y n - flOrbit M cubicCoeffs x₀ n|
--           ≤ gamma M.u 8 * hornerAbs cubicCoeffs B) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FloatExpandingShadowing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FloatExpandingShadowing.lean#L162

-- Thm stub generated from Novelty/FloatExpandingShadowing.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatExpandingShadowing
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

open Novelty.FloatBackwardError

open scoped BigOperators


/-! ### A concrete expanding polynomial dynamical system -/

theorem Novelty.FloatBackwardError.cubic_fl_shadowed_uniformly(M : RoundingModel) (x₀ B : ℝ) (N : ℕ)
    (hB : ∀ n ≤ N, |flOrbit M cubicCoeffs x₀ n| ≤ B) :
    ∃ y : ℕ → ℝ, (∀ n < N, cubicExpand (y n) = y (n + 1)) ∧
      (∀ n ≤ N, |y n - flOrbit M cubicCoeffs x₀ n|
        ≤ gamma M.u 8 * hornerAbs cubicCoeffs B) := by sorry
