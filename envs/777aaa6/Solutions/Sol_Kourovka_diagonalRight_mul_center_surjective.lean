-- Prove2me | solution 1 for Kourovka.diagonalRight_mul_center_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:03.56018+00:00
-- url     : https://prove2.me/submissions/425cc54f-2b87-4b5f-9a09-4e97eca8fd62

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
import Theorems.Thm_Kourovka_ProductHom_commute
import Theorems.Thm_Kourovka_ProductHom_row_surjective


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : A × B →* A × B)
    (hf : Function.Surjective f) (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∀ y, ∃ x z, z ∈ Subgroup.center B ∧ diagonalRight f x * z = y := by
  intro y
  let row := (MonoidHom.snd A B).comp f
  obtain ⟨a, b, hab⟩ := ProductHom.row_surjective row (Prod.snd_surjective.comp hf) y
  refine ⟨b, (f (a, 1)).2, h21 a, ?_⟩
  change ProductHom.right row b * ProductHom.left row a = y
  rw [← (ProductHom.commute row a b).eq]
  exact hab
end Kourovka
