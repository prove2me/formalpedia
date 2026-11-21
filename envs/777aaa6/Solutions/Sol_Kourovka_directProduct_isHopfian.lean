-- Prove2me | solution 1 for Kourovka.directProduct_isHopfian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:47:42.840178+00:00
-- url     : https://prove2.me/submissions/ee8fd7b2-f642-434b-aa74-df3bbc5a9b70

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
import Theorems.Thm_Kourovka_injective_of_positive_iterate
import Theorems.Thm_Kourovka_injective_of_central_offDiagonal_hopfian
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_surjective
import Theorems.Thm_Kourovka_exists_central_offDiagonal_iterate


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (hA : IsHopfian A) (hB : IsHopfian B) : IsHopfian (A × B) := by
  intro f hf
  obtain ⟨m, hm, h12, h21⟩ := exists_central_offDiagonal_iterate f hf
  have hi := injective_of_central_offDiagonal_hopfian hA hB (ProductPaths.iterateHom f m)
    (ProductPaths.iterateHom_surjective f hf m) h12 h21
  exact injective_of_positive_iterate f hm hi
end Kourovka
