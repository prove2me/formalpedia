-- Prove2me | solution 1 for Kourovka.ProductPaths.livePaths_middle_eq_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:44:23.676492+00:00
-- url     : https://prove2.me/submissions/45df6587-5591-4489-89ee-1643d8c4bfbd

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_livePaths_factorial_middle_eq_terminal

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ livePaths f, x m = x (2 * m) :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    livePaths_factorial_middle_eq_terminal f hf⟩
end Kourovka.ProductPaths
