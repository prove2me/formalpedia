-- Prove2me | Theorems.Thm_mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
-- name    : mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:02:44.490775+00:00
-- url     : https://prove2.me/theorems/9b641868-402c-4f72-8e54-6845cb58bd11
-- title:
--   DWZ Additional Zeroing-Out Step 1 yields the exact grouped compatibility cells
-- statement:
--   Let selected positions in a tensor power of $CW_q^{\otimes 2}$ carry literal nonzero fine blocks. Assume their fine left/right grades coarsen to the fifteen Table-2 shapes, that the surviving boundary $X$- and $Y$-fibres have the prescribed split histograms, and that the total coarse-$Z$/left-$Z$ histogram is the prescribed $\gamma$ histogram. Then Additional Zeroing-Out Step 1 forces the exact grouped compatibility cells:
--
--   $$
--   \#\{t:\operatorname{region}(\operatorname{outer}(t))=r,\;z_L(t)=a\}
--   =\operatorname{cellCount}(m,r,a)
--   $$
--
--   for every boundary-or-interior region $r$ and fine grade $a$. This capstone derives the missing $Z$-side compatibility conclusion from literal CW-square support and exact finite histograms, rather than assuming it as a certificate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Claim 6.2, Definition 6.3, and Additional Zeroing-Out Step 1 in Section 6.1. https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
import Theorems.Thm_mme_dwz_table2_step1_interior_z_histogram
import Theorems.Thm_mme_dwz_table2_boundary_interior_implies_grouped_compatibility

open MME MME.DWZStep1Support MME.DWZStep1Histogram

universe u

set_option autoImplicit false

theorem mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
    {K : Type u} [Field K] (q m : ℕ)
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (left right : Fin 3 → Position → Fin 3)
    (hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (![MME.DWZSquare.shapeX (outer t),
          MME.DWZSquare.shapeY (outer t),
          MME.DWZSquare.shapeZ (outer t)] i).val)
    (hFineSupport : ∀ t,
      (cwSquareFineSplitGrading K q).blockTensor
        (fun i => fineSplitGrade (left i t) (right i t)) ≠ 0)
    (hXSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hYSurvives : ∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hTotal : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber outer (left 2) k a) =
        table2TotalZSplit k a * m) :
    let groupedRegion :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s =>
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position // groupedRegion (outer t) = r ∧ left 2 t = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  sorry
