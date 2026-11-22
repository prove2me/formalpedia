-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_append
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:31.782071+00:00
-- url     : https://prove2.me/theorems/3ee319a7-5f66-4256-9ad1-33e67787ef4b
-- title:
--   Path In: append
-- statement:
--   The Path In construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L39-L45
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L39-L45

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.append {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X}
    (hx : PathIn f P p xs) (hy : PathIn f P (p + (xs.map f).sum) ys) :
    PathIn f P p (xs ++ ys) := by sorry
