-- Prove2me | solution 1 for mme_complete_split_count_test_iff_empirical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:17:21.665542+00:00
-- url     : https://prove2.me/submissions/21c8775b-1296-428e-abeb-8dd44633707f

import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

universe u

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped NNReal

theorem solution
    {ι : Type u} {ell N : ℕ} (hN : 0 < N)
    (label : ι → CompleteWord ell) (beta : Profile ell)
    (epsilon : ℝ≥0) (w : PowIndex ι N) :
    ApproxConsistent label beta epsilon w ↔
      ∀ sigma : CompleteWord ell,
        |(wordCount label w sigma : ℝ) / (N : ℝ) - beta.probability sigma| ≤
          (epsilon : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNR
  unfold ApproxConsistent
  apply forall_congr'
  intro sigma
  have heq : (wordCount label w sigma : ℝ) / (N : ℝ) - beta.probability sigma =
      ((wordCount label w sigma : ℝ) - (N : ℝ) * beta.probability sigma) / (N : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
  rw [mul_comm (epsilon : ℝ) (N : ℝ)]
