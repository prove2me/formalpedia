-- Prove2me | Theorems.Thm_Kourovka_centralCorrection_surjective
-- name    : Kourovka.centralCorrection_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:39.371644+00:00
-- url     : https://prove2.me/theorems/2faa0ae4-2a91-47b5-8325-43c034751fdd
-- title:
--   Kourovka: central Correction surjective
-- statement:
--   A correction through the center leaves surjectivity on the derived subgroup intact.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L26-L33
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L26-L33

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.centralCorrection_surjective (u : G →* G) (h : G →* Subgroup.center G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, u x = y)
    (hab : Function.Surjective (Abelianization.map (centralCorrection u h))) :
    Function.Surjective (centralCorrection u h) := by sorry
