-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:19:54.024184+00:00
-- url     : https://prove2.me/theorems/1adb57b3-7649-488f-8218-ca105ea1917c
-- title:
--   Schreier Heights: schreier Kernel Equiv of
-- statement:
--   The Schreier Heights construction uses the schreier Kernel Equiv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierKernel.lean#L61-L67
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierKernel.lean#L61-L67

import Definitions.Def_Kourovka_Halfspaces_HalfspaceRelators
import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [Group Q] (R : Set (FreeGroup X))
  (π : PresentedGroup R →* Q)

theorem Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of (S : Transversal (preKernel R π))
    (z : S.Edge) :
    (schreierKernelEquiv R π S (PresentedGroup.of z)).val =
      PresentedGroup.mk R (S.edgeValue z) := by sorry
