-- Prove2me | solution 1 for Kourovka.diagonalLeft_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:23.329009+00:00
-- url     : https://prove2.me/submissions/3b2ebec8-dd1f-4be8-aee6-7eb63451903e

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
import Theorems.Thm_Kourovka_ProductHom_left_center


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : A} (hz : z ∈ Subgroup.center A) : diagonalLeft f z ∈ Subgroup.center A :=
  ProductHom.left_center ((MonoidHom.fst A B).comp f) (Prod.fst_surjective.comp hf) hz
end Kourovka
