-- Prove2me | solution 1 for Kourovka.ProductPaths.finitePath_middle_eq_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:08.707179+00:00
-- url     : https://prove2.me/submissions/798d5ca7-7c97-4e1e-ad3e-bb4ae2896bf7

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_finitePath_factorial_middle_eq_terminal

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw :=
  ⟨(CenterWeight.weight (A × B)).factorial, Nat.factorial_pos _,
    finitePath_factorial_middle_eq_terminal f hf⟩
end Kourovka.ProductPaths
