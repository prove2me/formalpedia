-- Prove2me | solution 1 for Kourovka.ProductPaths.branch_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:47.453544+00:00
-- url     : https://prove2.me/submissions/40e3c0e3-2c06-4772-9778-ea4351510b0c

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
import Theorems.Thm_Kourovka_ProductPaths_axes_commute


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (k : A × B →* A × B)
    (p : (branch k false).range) (q : (branch k true).range) :
    Commute (p : k.range) (q : k.range) := by
  obtain ⟨x, hx⟩ := p.property
  obtain ⟨y, hy⟩ := q.property
  rw [← hx, ← hy]
  exact (axes_commute x y).map k.rangeRestrict
end Kourovka.ProductPaths
