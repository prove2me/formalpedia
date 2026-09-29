-- Prove2me | Theorems.Thm_mme_dwz_table2_equation23_numerator_count
-- name    : mme_dwz_table2_equation23_numerator_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T13:28:54.988927+00:00
-- url     : https://prove2.me/theorems/1c195a45-3a91-46f3-8468-90f40d8b75c2
-- title:
--   DWZ Equation (23): exact numerator cardinality
-- statement:
--   At the exact integral scale of DWZ Table 2, let
--   `SplitAssignments(m)` be the family of simultaneous three-label split words
--   on every boundary component and every interior $(+,+,k)$ region, with the
--   prescribed `split` and `plusSplit` fiber multiplicities multiplied by $m$.
--   Then
--
--   $$
--   |\operatorname{SplitAssignments}(m)|=
--   \left(\prod_{s:\,x(s)=0\ \mathrm{or}\ y(s)=0}
--     \operatorname{Mult}(\operatorname{split}_s m)\right)
--   \left(\prod_{k=0}^{4}
--     \operatorname{Mult}(\operatorname{plusSplit}_k m)\right).
--   $$
--
--   This is the exact finite numerator count for the independent conditions (a)
--   and (c) preceding DWZ Equation (23).  The disjointness of the regions is
--   encoded by tagged position types, and zero-mass rows and $m=0$ are included.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Lemma 6.7 and Equation (23), printed pp. 54–56.

import Definitions.Def_mme_dwz_table2_split_assignments

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_equation23_numerator_count (m : ℕ) :
    Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) =
      (∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
          Nat.multinomial Finset.univ
            (fun r => MME.DWZTable2Counts.split s r * m)
        else 1) *
      ∏ k : Fin 5,
        Nat.multinomial Finset.univ
          (fun r => MME.DWZTable2Counts.plusSplit k r * m) := by sorry
