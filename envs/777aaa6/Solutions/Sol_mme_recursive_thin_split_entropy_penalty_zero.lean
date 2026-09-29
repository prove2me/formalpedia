-- Prove2me | solution 1 for mme_recursive_thin_split_entropy_penalty_zero
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T22:13:51.961253+00:00
-- url     : https://prove2.me/submissions/ef826043-f895-4745-aca0-a0b9ec9a315c

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_recursive_thin_split_marginals_unique

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

theorem solution (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (alpha : Split half parent → ℝ)
    (hnonneg : ∀ a, 0 ≤ alpha a) (hsum : ∑ a, alpha a = 1) :
    SameMarginalDistributions alpha = {alpha} ∧
      (∀ rho ∈ SameMarginalDistributions alpha,
        (∑ a, Real.negMulLog (rho a)) = ∑ a, Real.negMulLog (alpha a)) ∧
      entropyPenalty alpha = 0 := by
  have hsingleton : SameMarginalDistributions alpha = {alpha} := by
    ext rho
    constructor
    · intro h
      exact mme_recursive_thin_split_marginals_unique half parent hthin rho alpha h.2.2
    · intro h
      have heq : rho = alpha := h
      subst rho
      exact ⟨hnonneg, hsum, fun _ _ ↦ rfl⟩
  refine ⟨hsingleton, ?_, ?_⟩
  · intro rho h
    have heq : rho = alpha := by rwa [hsingleton] at h
    rw [heq]
  · simp [entropyPenalty, hsingleton]
