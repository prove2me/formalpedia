-- Prove2me | Theorems.Thm_Novelty_FloatBackwardError_logistic_aposteriori_shadowing
-- name    : Novelty.FloatBackwardError.logistic_aposteriori_shadowing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:14:25.714216+00:00
-- url     : https://prove2.me/theorems/ed461aa0-3a90-4ceb-a30b-dd17815ede2c
-- title:
--   A-posteriori shadowing certificate for a binary64 logistic execution.
-- statement:
--   **A-posteriori shadowing certificate for a binary64 logistic execution.**
--   The exponential factor of `logistic_binary64_shadowing` is replaced by the
--   product of the *observed* local expansion factors `4 · max(xₖ, 1 - xₖ) ∈ [2,4]`,
--   a quantity computable from the execution itself.
--
--   ```lean
--   theorem Novelty.FloatBackwardError.logistic_aposteriori_shadowing(M : RoundingModel)
--       (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ)) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (N : ℕ)
--       (hstay : ∀ n ≤ N, flOrbit M logisticCoeffs x₀ n ∈ Set.Icc (0:ℝ) 1) :
--       ∀ n ≤ N, |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n|
--         ≤ errBound ((2:ℝ) ^ (-46 : ℤ))
--             (fun k => 4 * max (flOrbit M logisticCoeffs x₀ k)
--               (1 - flOrbit M logisticCoeffs x₀ k)) n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FloatShadowingSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FloatShadowingSharpness.lean#L196

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





/-! ### The a-posteriori bound for a binary64 logistic execution -/

theorem Novelty.FloatBackwardError.logistic_aposteriori_shadowing(M : RoundingModel)
    (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ)) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (N : ℕ)
    (hstay : ∀ n ≤ N, flOrbit M logisticCoeffs x₀ n ∈ Set.Icc (0:ℝ) 1) :
    ∀ n ≤ N, |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n|
      ≤ errBound ((2:ℝ) ^ (-46 : ℤ))
          (fun k => 4 * max (flOrbit M logisticCoeffs x₀ k)
            (1 - flOrbit M logisticCoeffs x₀ k)) n := by sorry
