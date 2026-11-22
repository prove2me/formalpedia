-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_path
-- name    : Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:21:14.860168+00:00
-- url     : https://prove2.me/theorems/d1157544-778a-4e0f-9934-c73e760338d5
-- title:
--   Schreier Heights: generator Word path
-- statement:
--   The Schreier Heights construction uses the generator Word path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L64-L80
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierPaths.lean#L64-L80

import Definitions.Def_Kourovka_Halfspaces_SchreierKernel
import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_path [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (θ : FreeGroup X →* Multiplicative ℝ) (S : Transversal L)
    (hheight : ∀ w, value θ (S.rep w) = value θ w)
    (P : ℝ → Prop) (z : S.Edge)
    (hz : z ∈ symbolsIn θ S P)
    (hfrom : PathIn (step θ) P 0 z.1.val.toWord)
    (hto : PathIn (step θ) P 0 (S.rep (z.1.val * FreeGroup.of z.2)).toWord) :
    PathIn (step θ) P 0 (generatorWord S z) := by sorry
