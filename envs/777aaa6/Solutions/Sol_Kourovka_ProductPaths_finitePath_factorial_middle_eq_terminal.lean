-- Prove2me | solution 1 for Kourovka.ProductPaths.finitePath_factorial_middle_eq_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:44:23.201158+00:00
-- url     : https://prove2.me/submissions/6115d1b2-d3bb-4a2b-9c97-2ad1064f4333

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_exists_livePath_extension
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_livePaths_factorial_middle_eq_terminal
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil



set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw := by
  let m := (CenterWeight.weight (A × B)).factorial
  change ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
    w[m]'(by omega) = w[2 * m]'hw
  intro w hw hn
  obtain ⟨x, hx, hwx⟩ := exists_livePath_extension f hf w hn
  have hp := livePaths_factorial_middle_eq_terminal f hf x hx
  have hget (i : ℕ) (hi : i < w.length) : w[i] = x i := by
    have hpref : w <+: initialWord w.length x := by rw [hwx]
    simpa only [initialWord, List.getElem_ofFn, FinitePaths.initialSegment] using hpref.getElem hi
  rw [hget m (by omega), hget (2 * m) hw]
  exact hp
end Kourovka.ProductPaths
