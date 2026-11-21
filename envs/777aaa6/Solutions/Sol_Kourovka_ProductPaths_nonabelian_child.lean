-- Prove2me | solution 1 for Kourovka.ProductPaths.nonabelian_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:59.192178+00:00
-- url     : https://prove2.me/submissions/e0dcef01-ed65-4bd0-93a6-95152b8de862

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_children_commute
import Theorems.Thm_Kourovka_ProductPaths_children_cover

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) :
    Nonabelian f (w ++ [false]) ∨ Nonabelian f (w ++ [true]) := by
  classical
  by_contra hn
  have hfalse : ∀ x y, Commute (path f (w ++ [false]) x) (path f (w ++ [false]) y) := by
    intro x y
    by_contra hxy
    exact hn (Or.inl ⟨x, y, hxy⟩)
  have htrue : ∀ x y, Commute (path f (w ++ [true]) x) (path f (w ++ [true]) y) := by
    intro x y
    by_contra hxy
    exact hn (Or.inr ⟨x, y, hxy⟩)
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨a, b, hab⟩ := children_cover f hf w x
  obtain ⟨c, d, hcd⟩ := children_cover f hf w y
  apply hxy
  rw [← hab, ← hcd]
  exact ((hfalse a c).mul_right (children_commute f w a d)).mul_left
    (((children_commute f w c b).symm).mul_right (htrue b d))
end Kourovka.ProductPaths
