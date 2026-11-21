-- Prove2me | Theorems.Thm_Kourovka_injective_of_central_offDiagonal
-- name    : Kourovka.injective_of_central_offDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:47.696778+00:00
-- url     : https://prove2.me/theorems/598d8e65-4c6d-4ca0-8c1a-eb457586b9f3
-- title:
--   Kourovka: injective of central off Diagonal
-- statement:
--   Central off-diagonal entries vanish on the derived factors, where the diagonal entries suffice.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L56-L92
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L56-L92

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.injective_of_central_offDiagonal [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B)
    (h11 : Set.InjOn (fun a => (f (a, 1)).1) (commutator A))
    (h22 : Set.InjOn (fun b => (f (1, b)).2) (commutator B)) :
    Function.Injective f := by sorry
