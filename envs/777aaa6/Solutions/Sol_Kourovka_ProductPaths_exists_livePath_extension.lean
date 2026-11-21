-- Prove2me | solution 1 for Kourovka.ProductPaths.exists_livePath_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:16.79885+00:00
-- url     : https://prove2.me/submissions/7377c944-a272-413e-a782-769c715a208a

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_extensionWord_nonabelian
import Theorems.Thm_Kourovka_ProductPaths_extensionWord_prefix
import Theorems.Thm_Kourovka_ProductPaths_initialWord_extensionStream
import Theorems.Thm_Kourovka_ProductPaths_nonabelian_of_prefix

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) :
    ∃ x ∈ livePaths f, initialWord w.length x = w := by
  refine ⟨extensionStream f w, ?_, ?_⟩
  · intro n
    rw [initialWord_extensionStream]
    exact nonabelian_of_prefix f (List.take_prefix n _)
      (extensionWord_nonabelian f hf w h n)
  · rw [initialWord_extensionStream]
    have hp : w <+: extensionWord f w w.length := extensionWord_prefix f w (Nat.zero_le _)
    exact (List.prefix_iff_eq_take.mp hp).symm
end Kourovka.ProductPaths
