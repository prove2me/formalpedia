-- Prove2me | Theorems.Thm_mme_complete_split_count_test_iff_empirical
-- name    : mme_complete_split_count_test_iff_empirical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T17:17:07.172466+00:00
-- url     : https://prove2.me/theorems/11a37057-71b7-43b6-af3d-ac605e0ffec2
-- title:
--   Complete-split count test matches empirical consistency
-- statement:
--   For a positive tensor-power length N, the scaled full-word count inequalities defining approximate complete-split consistency are equivalent to the source's pointwise empirical-frequency error bounds. This removes denominators without changing the Definition3.5-3.6 test; it makes no assertion for the source's undefined N=0 empirical distribution.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v3, printed pp.14-15, Definitions3.4-3.6. This is the finite all-mode projection layer; canonical CW labeling and the asymptotic degeneration/limit theorems remain separate.

import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Tactic

set_option autoImplicit false

universe u

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped NNReal

theorem mme_complete_split_count_test_iff_empirical
    {ι : Type u} {ell N : ℕ} (hN : 0 < N)
    (label : ι → CompleteWord ell) (beta : Profile ell)
    (epsilon : ℝ≥0) (w : PowIndex ι N) :
    ApproxConsistent label beta epsilon w ↔
      ∀ sigma : CompleteWord ell,
        |(wordCount label w sigma : ℝ) / (N : ℝ) - beta.probability sigma| ≤
          (epsilon : ℝ) := by sorry
