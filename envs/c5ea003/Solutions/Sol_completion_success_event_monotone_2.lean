-- Prove2me | solution 2 for completion_success_event_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:20.410302+00:00
-- url     : https://prove2.me/submissions/292b43f0-e913-49d5-a946-533ee71708df

import Definitions.Def_matrix_completion_basic

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' →
      IsUniqueMinimizer Omega M →
      IsUniqueMinimizer Omega' M := by
  intro Omega Omega' hsub hsuccess X hagree hne
  exact hsuccess X (fun p hp => hagree p (hsub hp)) hne

