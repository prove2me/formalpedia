-- Prove2me | Definitions.Def_Kourovka_PathWeight
-- name    : Kourovka_PathWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:31:36.991436+00:00
-- url     : https://prove2.me/theorems/4883dfd8-1b2b-4b7f-94b8-f4fe041c971f
-- title:
--   Path Weight
-- statement:
--   Definitions and structural lemmas for Path Weight, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathWeight.lean

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_path_append

set_option autoImplicit true
namespace Kourovka
namespace ProductPaths
variable {A B : Type*} [Group A] [Group B]
def branch (k : A × B →* A × B) (i : Bool) : A × B →* k.range :=
  k.rangeRestrict.comp (axis i)
theorem range_comp_surjective {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f) :
    (g.comp f).range = g.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  · rintro z ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩
noncomputable def branchEquiv (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (i : Bool) :
    (branch (path f w) i).range ≃* (path f (w ++ [i])).range :=
  (CenterWeight.rangeCompEquiv (branch (path f w) i) (path f w).range.subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr (by
      change ((path f w).comp (axis i)).range = (path f (w ++ [i])).range
      rw [path_append]
      change ((path f w).comp (axis i)).range =
        (((path f w).comp (axis i)).comp f).range
      exact (range_comp_surjective f ((path f w).comp (axis i)) hf).symm))
noncomputable def pathWeight (f : A × B →* A × B) (w : List Bool) : ℕ :=
  CenterWeight.weight (path f w).range
end ProductPaths
end Kourovka


