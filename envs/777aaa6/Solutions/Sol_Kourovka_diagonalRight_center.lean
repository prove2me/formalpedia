-- Prove2me | solution 1 for Kourovka.diagonalRight_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:46.262806+00:00
-- url     : https://prove2.me/submissions/4bd048b4-82a6-4b01-90a0-24b26eb3d6d5

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
import Theorems.Thm_Kourovka_ProductHom_right_center


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : B} (hz : z ∈ Subgroup.center B) : diagonalRight f z ∈ Subgroup.center B :=
  ProductHom.right_center ((MonoidHom.snd A B).comp f) (Prod.snd_surjective.comp hf) hz
end Kourovka
