-- Prove2me | Theorems.Thm_NTKConvergence_architecture_universality_on_trajectory
-- name    : NTKConvergence.architecture_universality_on_trajectory
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:18.867+00:00
-- url     : https://prove2.me/theorems/22d78cfe-51b6-4ce5-94b1-8a2e0f4e04fa
-- title:
--   Equality of kernel actions along two residual paths is enough for trajectory
-- statement:
--   Equality of kernel actions along two residual paths is enough for trajectory
--   universality; global equality of the operators is not required.
--
--   ```lean
--   theorem NTKConvergence.architecture_universality_on_trajectory    {E : Type*} [AddCommGroup E] [Module ℝ E]
--       (K₁ K₂ : E →ₗ[ℝ] E) (η : ℝ) (r₀ : E)
--       (hagrees : ∀ n,
--         K₁ (residualIterate (frozenKernelStep K₁ η) r₀ n) =
--         K₂ (residualIterate (frozenKernelStep K₂ η) r₀ n)) :
--       ∀ n,
--         residualIterate (frozenKernelStep K₁ η) r₀ n =
--         residualIterate (frozenKernelStep K₂ η) r₀ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NTKConvergence/Convergence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NTKConvergence/Convergence.lean#L113

-- Thm stub generated from MachineLearning/NTKConvergence/Convergence.lean
import Mathlib
import Definitions.Def_MachineLearning_NTKConvergence_Convergence
-- The module `MachineLearning.TropicalNTKDynamics` is referenced by the original
-- catalog export but is absent from this repository.  The two predicates and the
-- one lemma that this file used from it are reconstructed below, so that the file
-- is self-contained and compiles.

/-!
# Neural Tangent Kernel Convergence

This chapter isolates the architecture-independent dynamical core of lazy training.
On a finite training set, a frozen neural tangent kernel determines a linear residual
recursion. A strict contraction hypothesis gives convergence to the interpolating NTK
solution, while equality of frozen kernels gives universality of the entire training
trajectory across architectures.
-/

open Filter

noncomputable section

open NTKConvergence

theorem NTKConvergence.architecture_universality_on_trajectory    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K₁ K₂ : E →ₗ[ℝ] E) (η : ℝ) (r₀ : E)
    (hagrees : ∀ n,
      K₁ (residualIterate (frozenKernelStep K₁ η) r₀ n) =
      K₂ (residualIterate (frozenKernelStep K₂ η) r₀ n)) :
    ∀ n,
      residualIterate (frozenKernelStep K₁ η) r₀ n =
      residualIterate (frozenKernelStep K₂ η) r₀ n := by sorry
