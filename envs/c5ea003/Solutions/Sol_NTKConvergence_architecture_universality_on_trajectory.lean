-- Prove2me | solution 1 for NTKConvergence.architecture_universality_on_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:14.194403+00:00
-- url     : https://prove2.me/submissions/864fca37-4389-41da-a2e8-4042f38699c6

-- Sol generated from MachineLearning/NTKConvergence/Convergence.lean
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










open TropicalKernelDynamics






-- !-- Lab Notes -- !--
-- Hypothesis: (1) every frozen strict-contraction NTK converges geometrically;
-- (2) its rate is exactly spectral on eigendirections; (3) equal limiting kernels make
-- different architectures dynamically indistinguishable; (4) equality merely along
-- the realized paths already suffices; (5) tropical cell confinement supplies exact
-- lazy behavior; (6, bold) approximate kernel equality should imply quantitative
-- finite-horizon trajectory stability.
-- Experiment: the residual recursion was separated from neural parameter space. Claims
-- (1)--(5) survived; claim (6) was retained as a testable perturbation conjecture because
-- its sharp bound requires an additional Lipschitz/discrepancy framework.
-- Analysis: strict contraction is the analytic ingredient for interpolation, while
-- cell invariance is a geometric ingredient that freezes the kernel. The eigendirection
-- formula exposes the spectral factor `1 - ηλ` joining these two levels.
-- Critique: positive semidefiniteness alone does not imply strict contraction because
-- a kernel may have a nontrivial nullspace. Consequently the convergence theorem states
-- spectral contraction explicitly, concerns predictions rather than parameters, and
-- makes no unsupported infinite-width or probabilistic limit claim.
-- Synthesis: geometric decay, exact spectral dynamics, pathwise universality, and the
-- existing tropical cell criterion form an architecture-independent lazy-training
-- convergence principle for finite training sets.
-- !-- End Lab Notes -- !--


open NTKConvergence in
theorem solution    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K₁ K₂ : E →ₗ[ℝ] E) (η : ℝ) (r₀ : E)
    (hagrees : ∀ n,
      K₁ (residualIterate (frozenKernelStep K₁ η) r₀ n) =
      K₂ (residualIterate (frozenKernelStep K₂ η) r₀ n)) :
    ∀ n,
      residualIterate (frozenKernelStep K₁ η) r₀ n =
      residualIterate (frozenKernelStep K₂ η) r₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [residualIterate, residualIterate]
      unfold frozenKernelStep
      calc
        residualIterate (frozenKernelStep K₁ η) r₀ n -
            η • K₁ (residualIterate (frozenKernelStep K₁ η) r₀ n) =
          residualIterate (frozenKernelStep K₂ η) r₀ n -
            η • K₁ (residualIterate (frozenKernelStep K₁ η) r₀ n) := by rw [ih]
        _ = residualIterate (frozenKernelStep K₂ η) r₀ n -
            η • K₂ (residualIterate (frozenKernelStep K₂ η) r₀ n) := by
              rw [hagrees n]
