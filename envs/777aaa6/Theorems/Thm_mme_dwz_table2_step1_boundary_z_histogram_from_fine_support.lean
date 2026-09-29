-- Prove2me | Theorems.Thm_mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
-- name    : mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:39:30.890396+00:00
-- url     : https://prove2.me/theorems/cd996a8c-004e-4eb9-92b7-b6b804410250
-- title:
--   DWZ Step 1: fine CW support reflects boundary X/Y histograms into Z
-- statement:
--   Consider positions in a tensor power of $CW_q^{\otimes 2}$. Each position has one of the fifteen coarse Table-2 components and, in each tensor mode, a pair of fine grades whose sum is that coarse component grade. Assume every selected fine block is nonzero. For a boundary component—one whose $X$- or $Y$-grade is zero—the two half-support equations force the left $Z$-grade to be the reflected surviving $X$- or $Y$-grade. Consequently, if the surviving boundary $X$- and $Y$-fibres have the prescribed Table-2 split counts, then for every boundary component $s$ and split $a$,
--
--   $$
--   \#\{t : \operatorname{outer}(t)=s,\; z_L(t)=a\}
--   =\operatorname{split}(s,a)\,m.
--   $$
--
--   This is the boundary half of Additional Zeroing-Out Step 1. The hypotheses refer to literal nonzero blocks of the fine nine-grading of the squared CW tensor, rather than an abstract compatibility certificate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1, Claim 6.2 and Additional Zeroing-Out Step 1 (printed pp. 51--52 / PDF pp. 52--53). https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_table2_split_assignments

open MME MME.DWZStep1Support

universe u

set_option autoImplicit false

theorem mme_dwz_table2_step1_boundary_z_histogram_from_fine_support
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
          MME.DWZTable2Counts.split s a * m) :
    ∀ (s : Fin 15),
      MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position // outer t = s ∧ left 2 t = a} =
          MME.DWZTable2Counts.split s a * m := by
  sorry
