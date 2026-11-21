-- Prove2me | Theorems.Thm_Kourovka_surjective_of_derived_and_abelianization
-- name    : Kourovka.surjective_of_derived_and_abelianization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:17.079198+00:00
-- url     : https://prove2.me/theorems/ea52b037-7106-4fda-916d-afb1d18f28e4
-- title:
--   Kourovka: surjective of derived and abelianization
-- statement:
--   Surjectivity on the derived subgroup and on abelianization implies surjectivity.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L12-L23
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L12-L23

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.surjective_of_derived_and_abelianization (f : G →* G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, f x = y)
    (hab : Function.Surjective (Abelianization.map f)) : Function.Surjective f := by sorry
