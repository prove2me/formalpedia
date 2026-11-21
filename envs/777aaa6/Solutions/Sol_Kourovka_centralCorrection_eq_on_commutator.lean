-- Prove2me | solution 1 for Kourovka.centralCorrection_eq_on_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:32.534798+00:00
-- url     : https://prove2.me/submissions/2c8eadc5-59ff-43ad-b927-9aa20b611e78

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
import Theorems.Thm_Kourovka_central_map_kills_commutator

set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
namespace Kourovka
theorem _root_.solution (u : A →* A) (h : A →* Subgroup.center A)
    {a : A} (ha : a ∈ commutator A) : centralCorrection u h a = u a := by
  have hc : (Subgroup.center A).subtype.comp h a = 1 :=
    central_map_kills_commutator ((Subgroup.center A).subtype.comp h)
      (fun x => (h x).property) ha
  change u a * ↑(h a) = u a
  change ↑(h a) = (1 : A) at hc
  rw [hc, mul_one]
end Kourovka
