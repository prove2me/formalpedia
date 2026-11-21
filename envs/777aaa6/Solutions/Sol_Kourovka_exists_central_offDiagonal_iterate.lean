-- Prove2me | solution 1 for Kourovka.exists_central_offDiagonal_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:58.076701+00:00
-- url     : https://prove2.me/submissions/4c8b8abd-4beb-484e-b8ee-d0d32e9a6844

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
import Theorems.Thm_Kourovka_central_offDiagonal_factorial_iterate

set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧
      (∀ b : B, (ProductPaths.iterateHom f m (1, b)).1 ∈ Subgroup.center A) ∧
      (∀ a : A, (ProductPaths.iterateHom f m (a, 1)).2 ∈ Subgroup.center B) :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    central_offDiagonal_factorial_iterate f hf⟩
end Kourovka
