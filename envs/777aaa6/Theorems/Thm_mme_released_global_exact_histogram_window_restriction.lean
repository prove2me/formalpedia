-- Prove2me | Theorems.Thm_mme_released_global_exact_histogram_window_restriction
-- name    : mme_released_global_exact_histogram_window_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:57:11.852688+00:00
-- url     : https://prove2.me/theorems/afc63e94-75df-4027-b1dc-139ac09edf17
-- title:
--   Exact released histograms restrict from normalized global cell windows
-- statement:
--   For every positive-length released coarse cell, its exact marginal histogram tensor restricts from the actual normalized cell window at every nonnegative tolerance.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_exact_histogram_window_restriction
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ)
    (c : Cell 8 1 (fun _ _ ↦ 8)) (hL : 0 < k * coarseCounts owner c.2)
    (eps : ℝ) (heps : 0 ≤ eps) :
    let L := k * coarseCounts owner c.2
    Restrict
      (unbroken K 5 3 L (Equiv.refl _) (fun _ => Unit.unit)
        (fun _ i => (c.2.val i).val) (fun i _ w => k * wordCounts owner i c.2 w))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)) := by sorry
