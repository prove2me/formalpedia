-- Prove2me | solution 1 for Kourovka.central_offDiagonal_factorial_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:02.944681+00:00
-- url     : https://prove2.me/submissions/2bab8dba-4350-4b0b-8b8a-d5655fef785b

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
import Theorems.Thm_Kourovka_first_offDiagonal_central_of_killed
import Theorems.Thm_Kourovka_second_offDiagonal_central_of_killed
import Theorems.Thm_Kourovka_ProductPaths_factorial_mixed_iterate_central
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_surjective


set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    (∀ b : B, (ProductPaths.iterateHom f m (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (ProductPaths.iterateHom f m (a, 1)).2 ∈ Subgroup.center B) := by
  let m := (CenterWeight.weight (A × B)).factorial
  have hmix := ProductPaths.factorial_mixed_iterate_central f hf
  let F := ProductPaths.iterateHom f m
  have hF : Function.Surjective F := ProductPaths.iterateHom_surjective f hf m
  have hk1 : ∀ b : B, F ((F (1, b)).1, 1) ∈ Subgroup.center (A × B) := by
    intro b
    exact hmix false true (by decide) (1, b)
  have hk2 : ∀ a : A, F (1, (F (a, 1)).2) ∈ Subgroup.center (A × B) := by
    intro a
    exact hmix true false (by decide) (a, 1)
  exact ⟨first_offDiagonal_central_of_killed F hF hk1,
    second_offDiagonal_central_of_killed F hF hk2⟩
end Kourovka
