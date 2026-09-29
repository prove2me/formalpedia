-- Prove2me | Theorems.Thm_Novelty_FloatBackwardError_finite_shadowing_sharp
-- name    : Novelty.FloatBackwardError.finite_shadowing_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:14:07.289279+00:00
-- url     : https://prove2.me/theorems/63f7ee78-8ac5-4e74-9738-385516dc1094
-- title:
--   The forward shadowing bound is attained.
-- statement:
--   **The forward shadowing bound is attained.**  For every `L ≥ 0` and every
--   `δ ≥ 0` there is an exactly `L`-Lipschitz map and a pseudo-orbit whose local
--   defect is exactly `δ` at each step, whose distance from the true orbit through
--   the same initial point equals `δ (1 + L + ⋯ + L^{n-1})` for every `n`.  Hence
--   `finite_shadowing` is optimal.
--
--   ```lean
--   theorem Novelty.FloatBackwardError.finite_shadowing_sharp(L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ) :
--       ∃ (f : ℝ → ℝ) (x : ℕ → ℝ),
--         (∀ a b : ℝ, |f a - f b| = L * |a - b|) ∧
--         (∀ n : ℕ, |x (n + 1) - f (x n)| = δ) ∧
--         (∀ n : ℕ, |x n - trueOrbit f (x 0) n| = δ * ∑ k ∈ Finset.range n, L ^ k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FloatShadowingSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FloatShadowingSharpness.lean#L121

-- Thm stub generated from Novelty/FloatShadowingSharpness.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Definitions.Def_Novelty_FloatShadowingSharpness

/-!
# Nonautonomous shadowing bounds and their sharpness

Third cycle of the programme.  Two questions left open by the previous cycles
are settled here.

1. *Is the uniform Lipschitz constant necessary?*  No: `variable_shadowing`
   replaces `L` by the observed, step-dependent local expansion factors `L n`,
   producing the a-posteriori error recursion `E 0 = 0`,
   `E (n+1) = δ + L n · E n`.  Specialising to a constant sequence recovers the
   geometric bound (`errBound_const`), so the nonautonomous statement is a
   strict refinement.

2. *Is the exponential growth of the forward bound an artifact of the proof?*
   No: `finite_shadowing_sharp` exhibits, for every `L ≥ 0` and `δ ≥ 0`, an
   `L`-Lipschitz map and a `δ`-pseudo-orbit for which the distance to the true
   orbit **equals** `δ (1 + L + ⋯ + L^{n-1})` at every step.  Hence the forward
   shadowing theorem of the first cycle cannot be improved, and the improvement
   obtained in the second cycle (`expanding_backward_shadowing`) genuinely
   requires moving the initial condition.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the geometric factor in forward shadowing is exactly
attained by the linear map `z ↦ L z` driven by a constant defect `δ`, so no
proof technique can remove it while keeping the initial point fixed.
Experiment (Experimenter): the witness is the affine recursion
`x_{n+1} = L xₙ + δ` started at `0`, whose true orbit is identically `0`; the
distance is the geometric sum, verified by induction (`sharpWitness_eq`).
Analysis (Analyst): the three cycles now separate cleanly:
semantics (`O(u)` defect) → forward dynamics (`O(u · Lⁿ)`, sharp) →
backward dynamics under expansivity (`O(u)`, uniform in n).
Critique (Critic): the sharpness witness is an honest pseudo-orbit — its defect
is exactly `δ` at every step, not merely bounded by `δ` — and the map is exactly
`L`-Lipschitz, so no slack is hidden in the hypotheses.
-- !-- End Lab Notes -- !--
-/

open Novelty.FloatBackwardError

open scoped BigOperators





/-! ### Sharpness of the forward shadowing bound -/

theorem Novelty.FloatBackwardError.finite_shadowing_sharp(L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ) :
    ∃ (f : ℝ → ℝ) (x : ℕ → ℝ),
      (∀ a b : ℝ, |f a - f b| = L * |a - b|) ∧
      (∀ n : ℕ, |x (n + 1) - f (x n)| = δ) ∧
      (∀ n : ℕ, |x n - trueOrbit f (x 0) n| = δ * ∑ k ∈ Finset.range n, L ^ k) := by sorry
