-- Prove2me | solution 1 for Kourovka.injective_of_central_offDiagonal_hopfian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:50.063485+00:00
-- url     : https://prove2.me/submissions/f45cd846-4203-46ea-9312-8311608345b0

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
import Theorems.Thm_Kourovka_diagonalLeft_center
import Theorems.Thm_Kourovka_diagonalRight_center
import Theorems.Thm_Kourovka_diagonalLeft_mul_center_surjective
import Theorems.Thm_Kourovka_diagonalRight_mul_center_surjective
import Theorems.Thm_Kourovka_injective_of_positive_iterate
import Theorems.Thm_Kourovka_CentralLattice_exists_group_correction_modulus
import Theorems.Thm_Kourovka_CentralProductPowers_diagonal_surjective_on_derived
import Theorems.Thm_Kourovka_CentralProductPowers_iterate_central_offDiagonal
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_surjective
import Theorems.Thm_Kourovka_centralCorrection_injective_on_derived
import Theorems.Thm_Kourovka_exists_diagonal_congruence_iterate
import Theorems.Thm_Kourovka_injective_of_central_offDiagonal


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    (hA : IsHopfian A) (hB : IsHopfian B)
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) : Function.Injective f := by
  obtain ⟨dA, hdA, hmodA⟩ := CentralLattice.exists_group_correction_modulus (G := A)
  obtain ⟨dB, hdB, hmodB⟩ := CentralLattice.exists_group_correction_modulus (G := B)
  obtain ⟨n, hn, hcongA, hcongB⟩ := exists_diagonal_congruence_iterate f hf dA dB hdA hdB
  let F := ProductPaths.iterateHom f n
  have hF : Function.Surjective F := ProductPaths.iterateHom_surjective f hf n
  obtain ⟨hF12, hF21⟩ := CentralProductPowers.iterate_central_offDiagonal f hf h12 h21 n
  obtain ⟨hderA, hderB⟩ := CentralProductPowers.diagonal_surjective_on_derived F hF hF12 hF21
  obtain ⟨cA, hcA⟩ := hmodA (diagonalLeft F)
    (fun _ hz => diagonalLeft_center F hF hz)
    (diagonalLeft_mul_center_surjective F hF hF12) hcongA hderA
  obtain ⟨cB, hcB⟩ := hmodB (diagonalRight F)
    (fun _ hz => diagonalRight_center F hF hz)
    (diagonalRight_mul_center_surjective F hF hF21) hcongB hderB
  have hiA := centralCorrection_injective_on_derived hA (diagonalLeft F) cA hcA
  have hiB := centralCorrection_injective_on_derived hB (diagonalRight F) cB hcB
  have hiF := injective_of_central_offDiagonal F hF hF12 hF21 hiA hiB
  exact injective_of_positive_iterate f hn hiF
end Kourovka
