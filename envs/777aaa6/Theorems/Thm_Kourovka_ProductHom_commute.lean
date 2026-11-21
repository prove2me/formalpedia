-- Prove2me | Theorems.Thm_Kourovka_ProductHom_commute
-- name    : Kourovka.ProductHom.commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:46.834624+00:00
-- url     : https://prove2.me/theorems/b9dd22af-d6cc-46a2-855f-3b4aeaef1176
-- title:
--   Product Hom: commute
-- statement:
--   The Product Hom construction uses the commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L26-L30
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L26-L30

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom

theorem Kourovka.ProductHom.commute (f : A × B →* K) (a : A) (b : B) :
    Commute (left f a) (right f b) := by sorry
