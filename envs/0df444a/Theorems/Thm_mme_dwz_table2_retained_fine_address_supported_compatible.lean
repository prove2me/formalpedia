-- Prove2me | Theorems.Thm_mme_dwz_table2_retained_fine_address_supported_compatible
-- name    : mme_dwz_table2_retained_fine_address_supported_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:31:02.201352+00:00
-- url     : https://prove2.me/theorems/44561421-b7ea-4250-958d-5f5d15918114
-- title:
--   Supported retained fine addresses satisfy literal Table-2 compatibility
-- statement:
--   Let a family of retained Table-2 component words share one coarse $Z$ word and be isolated by their $Y$ words. Refine every mode and tensor-power position by the canonical nine-grading of $CW_q\otimes CW_q$. Assume the fine labels coarsen to the outer Table-2 shapes, every retained copy has the prescribed boundary $X$ and $Y$ split histograms, and every retained fine $Z$ word has the prescribed total-Z histogram.
--
--   For any mixed choice $(j_0,j_1,j_2)$ whose fine block is nonzero at every position, the fine $Z$ word of $j_2$ is compatible with the retained outer word of $j_0$ in every boundary component and every grouped interior $(+,+,k)$ region. Equivalently,
--
--   $$
--   \operatorname{Compatible}_m(\operatorname{outer}_{j_0},z_{j_2})
--   $$
--
--   with the exact Table-2 cell counts. This supplies the source-facing `hSupportedCompatible` premise of the Step-2 nonhole direct-sum restriction without replacing support by dimensions or assuming a hole mask.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.2 and Additional Zeroing-Out Step 1, printed pp. 51--52 (PDF pp. 52--53), with grouped compatibility from Definition 6.1 and Equation (23); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Theorems.Thm_mme_dwz_table2_retained_fine_address_xy_owner
import Theorems.Thm_mme_dwz_table2_step1_fine_support_implies_grouped_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_retained_fine_address_supported_compatible
    (K : Type u) [Field K] (q m : ℕ)
    {Copy Position : Type*} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (left right : Copy → Fin 3 → Position → Fin 3)
    (hCoarse : ∀ j i r,
      (left j i r).val + (right j i r).val =
        (cwSquareBlockType
          (DWZSquare.shapeX (outer j r))
          (DWZSquare.shapeY (outer j r))
          (DWZSquare.shapeZ (outer j r)) i).val)
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
        (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j')
    (hXSurvives : ∀ j (s : Fin 15), DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧ (left j 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hYSurvives : ∀ j (s : Fin 15), DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧ (left j 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hTotal : ∀ j (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber (outer j) (left j 2) k a) =
        table2TotalZSplit k a * m) :
    ∀ js : Fin 3 → Copy,
      (∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      retainedFineCompatible m outer
        (retainedFineAddress left right (js 2) 2) (js 0) := by
  sorry
