-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_lattice_kernel_finite_module
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_module
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:12:56.050187+00:00
-- url     : https://prove2.me/theorems/c81adc6e-3f3b-48f9-961e-0ec3ec655b49
-- title:
--   Cofinal Cover: lattice kernel finite module
-- statement:
--   The Cofinal Cover construction uses the lattice kernel finite module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/LatticePullback.lean#L77-L87
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/LatticePullback.lean#L77-L87

import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Cofinality_LatticePullback
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule

theorem Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_module {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    letI := lattice_kernel_commutative R hG
    letI := laurentModule (latticeProjection R) (latticeProjection_surjective R)
      (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (AddMonoidAlgebra ℤ (Lattice k)) (Additive (latticeProjection R).ker) := by sorry
