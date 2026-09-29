-- Prove2me | solution 1 for completion_success_event_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:07:41.289579+00:00
-- url     : https://prove2.me/submissions/44530bb8-6ff0-4463-9a55-4c6e9a264efb

import Definitions.Def_matrix_completion_basic
open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' →
      IsUniqueMinimizer Omega M →
      IsUniqueMinimizer Omega' M := by
  intro Omega Omega' hsub hmin X hagree hne
  exact hmin X (fun p hp => hagree p (hsub hp)) hne
