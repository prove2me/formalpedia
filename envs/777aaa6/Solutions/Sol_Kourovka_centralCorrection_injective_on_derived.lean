-- Prove2me | solution 1 for Kourovka.centralCorrection_injective_on_derived
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:23.576208+00:00
-- url     : https://prove2.me/submissions/3000ec96-923f-4935-82c6-c37dc7958595

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
import Theorems.Thm_Kourovka_centralCorrection_eq_on_commutator


set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (hG : IsHopfian G)
    (u : G →* G) (h : G →* Subgroup.center G)
    (hsurj : Function.Surjective (centralCorrection u h)) :
    Set.InjOn u (commutator G) := by
  intro x hx y hy heq
  apply hG (centralCorrection u h) hsurj
  simpa only [centralCorrection_eq_on_commutator u h hx,
    centralCorrection_eq_on_commutator u h hy] using heq
end Kourovka
