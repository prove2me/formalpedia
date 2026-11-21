-- Prove2me | solution 1 for Kourovka.ProductPaths.branch_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:47.894604+00:00
-- url     : https://prove2.me/submissions/fcb5fa5a-35d7-410c-89cd-c113aab90e05

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
import Theorems.Thm_Kourovka_ProductPaths_axis_product


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (k : A × B →* A × B) (g : k.range) :
    ∃ p : (branch k false).range, ∃ q : (branch k true).range,
      (p : k.range) * q = g := by
  obtain ⟨x, hx⟩ := k.rangeRestrict_surjective g
  refine ⟨⟨branch k false x, ⟨x, rfl⟩⟩, ⟨branch k true x, ⟨x, rfl⟩⟩, ?_⟩
  change k.rangeRestrict (axis false x) * k.rangeRestrict (axis true x) = g
  rw [← map_mul, axis_product, hx]
end Kourovka.ProductPaths
