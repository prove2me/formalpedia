-- Prove2me | Theorems.Thm_Kourovka_ProductHom_left_center
-- name    : Kourovka.ProductHom.left_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:43.496401+00:00
-- url     : https://prove2.me/theorems/c43271b2-f9ff-4398-8396-7347cfa652ed
-- title:
--   Product Hom: left center
-- statement:
--   The Product Hom construction uses the left center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L37-L44
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L37-L44

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom

theorem Kourovka.ProductHom.left_center (f : A × B →* K) (hf : Function.Surjective f)
    {a : A} (ha : a ∈ Subgroup.center A) : left f a ∈ Subgroup.center K := by sorry
