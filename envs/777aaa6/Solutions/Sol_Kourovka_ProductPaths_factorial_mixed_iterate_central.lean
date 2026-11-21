-- Prove2me | solution 1 for Kourovka.ProductPaths.factorial_mixed_iterate_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:08.206656+00:00
-- url     : https://prove2.me/submissions/2c86494f-9d19-404b-8d02-8765c479d47d

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
import Theorems.Thm_Kourovka_ProductPaths_mixed_term_central
import Theorems.Thm_Kourovka_ProductPaths_allWords_length
import Theorems.Thm_Kourovka_ProductPaths_finitePath_factorial_middle_eq_terminal
import Theorems.Thm_Kourovka_ProductPaths_path_expansion


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
      f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B) := by
  let m := (CenterWeight.weight (A × B)).factorial
  have hm : 0 < m := Nat.factorial_pos _
  have hp := finitePath_factorial_middle_eq_terminal f hf
  change ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
    f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B)
  intro j k hjk x
  let g : A × B →* A × B := (iterateHom f m).comp (axis j)
  change g (f^[m] (axis k x)) ∈ _
  rw [← path_expansion f m (axis k x), g.map_list_prod]
  apply Subgroup.list_prod_mem
  intro t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
  change f^[m] (axis j (path f v (axis k x))) ∈ _
  rw [← path_expansion]
  apply Subgroup.list_prod_mem
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact mixed_term_central f hf m hm hp u v (allWords_length _ _ hu)
    (allWords_length _ _ hv) j k hjk x
end Kourovka.ProductPaths
