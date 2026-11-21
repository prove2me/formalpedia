-- Prove2me | solution 1 for Kourovka.second_offDiagonal_central_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:44.20795+00:00
-- url     : https://prove2.me/submissions/3b370625-911e-476d-a8d0-503579694d6c

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
import Theorems.Thm_Kourovka_first_offDiagonal_central_of_killed

set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B] [IsSolvable B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ a : A, f (1, (f (a, 1)).2) ∈ Subgroup.center (A × B)) :
    ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B := by
  let e : A × B ≃* B × A := MulEquiv.prodComm
  let g : B × A →* B × A := e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hg : Function.Surjective g := e.surjective.comp (hf.comp e.symm.surjective)
  have hkg : ∀ a : A, g ((g (1, a)).1, 1) ∈ Subgroup.center (B × A) := by
    intro a
    exact (Subgroup.centerCongr e ⟨f (1, (f (a, 1)).2), hk a⟩).property
  exact first_offDiagonal_central_of_killed g hg hkg
end Kourovka
