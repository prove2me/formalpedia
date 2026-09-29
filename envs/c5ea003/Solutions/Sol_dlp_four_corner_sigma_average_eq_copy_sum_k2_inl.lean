-- Prove2me | solution 1 for dlp_four_corner_sigma_average_eq_copy_sum_k2_inl
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:32:46.287709+00:00
-- url     : https://prove2.me/submissions/222b3d20-00ce-4a83-a970-ebb5e940cb3c

import Definitions.Def_dlp_sigma_randomization
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Fin

open MatrixCompletion
open scoped BigOperators Classical

theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → V) :
    (1 / 4 : ℝ) • ∑ b₁ : Fin 2, ∑ b₂ : Fin 2,
        (4 : ℝ) • f
          (dlpCopyPerm (if b₁ = 0 then (1 : ℝ) else -1) l₁)
          (dlpCopyPerm (if b₂ = 0 then (1 : ℝ) else -1) l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, f j₁ j₂ := by
  have hne : ((-1 : ℝ) = 1) = False := by norm_num
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp [dlpCopyPerm, Fin.sum_univ_two, Fin.rev, hne] <;>
    abel
