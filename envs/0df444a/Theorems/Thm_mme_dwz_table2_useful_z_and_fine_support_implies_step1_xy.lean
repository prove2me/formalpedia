-- Prove2me | Theorems.Thm_mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy
-- name    : mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:00:32.358824+00:00
-- url     : https://prove2.me/theorems/986ba9e4-1054-493f-bea7-1ac53a8801b5
-- title:
--   A useful Z word absorbs the DWZ Step-1 X/Y filters
-- statement:
--   Let a fine word in $CW_q^{\otimes2}$ coarsen to one Table-2 component word and be coordinatewise supported. Suppose its fine $Z$ word has the prescribed useful-block histogram. Then the fine $X$ word automatically has every boundary histogram required when the coarse $Y$ grade is zero, and the fine $Y$ word automatically has every boundary histogram required when the coarse $X$ grade is zero. Equivalently, on boundary components,
--
--   $$x_L(t)+a=2\iff z_L(t)=a,\qquad y_L(t)+a=2\iff z_L(t)=a.$$
--
--   Thus the Additional Zeroing-Out Step-1 $X/Y$ projectors are redundant on a diagonal tensor term carrying a useful $Z$ word, while remaining available to eliminate mixed-owner terms.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.1, Additional Zeroing-Out Step 1 and Claim 6.2, pp. 51--52.

import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

open MME MME.DWZStep1Support

universe u

set_option autoImplicit false

theorem mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy
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
        (fun i ↦ fineSplitGrade (left i t) (right i t)) ≠ 0)
    (hZUseful : ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card {t : Position // outer t = s ∧ left 2 t = a} =
        MME.DWZTable2Counts.split s a * m) :
    (∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧ (left 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) := by
  sorry
