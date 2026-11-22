-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_lattice_kernel_finite_normal_generators
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_normal_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:12:39.019183+00:00
-- url     : https://prove2.me/theorems/910ec3f0-b91f-45c5-84e1-b6fe91f03316
-- title:
--   Cofinal Cover: lattice kernel finite normal generators
-- statement:
--   The Cofinal Cover construction uses the lattice kernel finite normal generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/LatticePullback.lean#L62-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/LatticePullback.lean#L62-L75

import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Cofinality_LatticePullback
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule

theorem Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_normal_generators {k : ℕ} (R : List (FreeGroup (Fin k))) :
    ∃ s : Finset (latticeProjection R).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (latticeProjection R).ker)) =
        (latticeProjection R).ker := by sorry
