-- Prove2me | Theorems.Thm_Kourovka_ProductHom_right_center
-- name    : Kourovka.ProductHom.right_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:28:45.951634+00:00
-- url     : https://prove2.me/theorems/d614fa98-7a2d-4b12-9f18-9978149d2bfc
-- title:
--   Product Hom: right center
-- statement:
--   The Product Hom construction uses the right center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L46-L53
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Components.lean#L46-L53

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom

theorem Kourovka.ProductHom.right_center (f : A × B →* K) (hf : Function.Surjective f)
    {b : B} (hb : b ∈ Subgroup.center B) : right f b ∈ Subgroup.center K := by sorry
