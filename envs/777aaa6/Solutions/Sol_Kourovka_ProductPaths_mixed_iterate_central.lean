-- Prove2me | solution 1 for Kourovka.ProductPaths.mixed_iterate_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:03.342011+00:00
-- url     : https://prove2.me/submissions/38a3ddee-67f1-48b4-be93-8e924b3627a4

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
import Theorems.Thm_Kourovka_ProductPaths_factorial_mixed_iterate_central

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
      f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B) :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    factorial_mixed_iterate_central f hf⟩
end Kourovka.ProductPaths
