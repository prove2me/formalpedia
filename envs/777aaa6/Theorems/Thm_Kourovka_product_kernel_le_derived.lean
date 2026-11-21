-- Prove2me | Theorems.Thm_Kourovka_product_kernel_le_derived
-- name    : Kourovka.product_kernel_le_derived
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:45.783723+00:00
-- url     : https://prove2.me/theorems/9fa503ce-919d-401a-8cb4-2a83079a0cfa
-- title:
--   Kourovka: product kernel le derived
-- statement:
--   The kernel of a surjective product endomorphism lies in the product of derived subgroups.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L46-L53
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L46-L53

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.product_kernel_le_derived [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) :
    f.ker ≤ (commutator A).prod (commutator B) := by sorry
