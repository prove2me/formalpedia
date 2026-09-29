-- Prove2me | solution 1 for mme_released_recursive_profile_identity
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:56.975363+00:00
-- url     : https://prove2.me/submissions/596040fa-9234-4e12-b6b6-e9710c9adc57

import Theorems.Thm_mme_released_global_sparse_marginals
import Theorems.Thm_mme_released_recursive_profile_normalization
import Theorems.Thm_mme_released_recursive_profile_counts_0
import Theorems.Thm_mme_released_recursive_profile_counts_1
import Theorems.Thm_mme_released_recursive_profile_counts_2
import Theorems.Thm_mme_released_recursive_profile_counts_3
import Theorems.Thm_mme_released_recursive_profile_counts_4
import Theorems.Thm_mme_released_recursive_profile_counts_5
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
set_option maxRecDepth 3000

attribute [local irreducible] alpha term roles parentCount parentProfile wordCounts jointRows atom shapeEquiv

private theorem reconstructed (o : Fin 6) (s : Fin 45) (i : Fin 3) (w : Word) :
    ((jointRows o s).map (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum =
      parentCount (term o s) (roles o i) w := by
  fin_cases o
  · exact mme_released_recursive_profile_counts_0 s i w
  · exact mme_released_recursive_profile_counts_1 s i w
  · exact mme_released_recursive_profile_counts_2 s i w
  · exact mme_released_recursive_profile_counts_3 s i w
  · exact mme_released_recursive_profile_counts_4 s i w
  · exact mme_released_recursive_profile_counts_5 s i w

theorem solution (o : Fin 6) (i : Fin 3) (c : Shape) (w : Word) :
    wordCounts o i c w = alpha o (shapeEquiv.symm c) *
      parentCount (term o (shapeEquiv.symm c)) (roles o i) w ∧
    (profile o).2 i ⟨0,c⟩ w =
      ((alpha o (shapeEquiv.symm c) : ℝ) / D) *
        parentProfile (term o (shapeEquiv.symm c)) (roles o i) w := by
  have h := (mme_released_global_sparse_marginals o c i w).trans
    (congrArg (fun n ↦ alpha o (shapeEquiv.symm c) * n)
      (reconstructed o (shapeEquiv.symm c) i w))
  refine ⟨h, ?_⟩
  change (wordCounts o i c w : ℝ) / (D : ℝ)^5 = _
  rw [h, Nat.cast_mul, ← mme_released_recursive_profile_normalization]
  ring
