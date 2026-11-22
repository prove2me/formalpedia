-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_endpoint
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:12:30.039687+00:00
-- url     : https://prove2.me/theorems/b3bbcbc0-b906-4ce2-aa83-0980997ca39a
-- title:
--   Path In: endpoint
-- statement:
--   The Path In construction uses the endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L33-L37
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L33-L37

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.endpoint {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : P (p + (xs.map f).sum) := by sorry
