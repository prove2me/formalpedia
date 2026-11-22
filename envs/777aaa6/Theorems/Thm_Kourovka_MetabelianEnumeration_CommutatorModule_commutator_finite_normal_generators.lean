-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_commutator_finite_normal_generators
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.commutator_finite_normal_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:01.73466+00:00
-- url     : https://prove2.me/theorems/4a0754fa-252e-41fb-9e91-0282d288e8b2
-- title:
--   Commutator Module: commutator finite normal generators
-- statement:
--   The Commutator Module construction uses the commutator finite normal generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L21-L38
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L21-L38

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.commutator_finite_normal_generators (R : List (FreeGroup α)) :
    ∃ s : Finset (PresentedGroup (CentralExtension.relSet R)),
      Subgroup.normalClosure (s : Set (PresentedGroup (CentralExtension.relSet R))) =
        commutator (PresentedGroup (CentralExtension.relSet R)) := by sorry
