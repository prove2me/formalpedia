-- Prove2me | Theorems.Thm_mme_released_global_compatibility_rows
-- name    : mme_released_global_compatibility_rows
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:11:32.673687+00:00
-- url     : https://prove2.me/theorems/20cf59b1-0df4-432a-9df6-d47351fc0de8
-- title:
--   Matched rational rows compute the actual outer compatibility potential
-- statement:
--   Rational boundary rows and pooled interior rows matched to the actual profile give its complete compatibility potential. Boundary cells remain separate, and interior classes retain their coarse coordinate. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedGlobal MME.RecursiveYZ

theorem mme_released_global_compatibility_rows
    (owner : Fin 6) (i : Fin 2) (x : (Fin 45 ⊕ Fin 9) → Word → ℚ)
    (hb : ∀ s w, (x (Sum.inl s) w : ℝ) =
      if yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, shapeEquiv s⟩ then
        (profile owner).2 (yzMode i) ⟨0, shapeEquiv s⟩ w else 0)
    (hi : ∀ j w, (x (Sum.inr j) w : ℝ) =
      ∑ c : Shape, if ¬ yzBoundary (half := 8) (parent := fun (_ : Fin 1) (_ : Fin 3) ↦ 8) i ⟨0, c⟩ ∧ c.val (yzMode i) = j then
        (profile owner).2 (yzMode i) ⟨0, c⟩ w else 0) :
    (profile owner).compat i 0 =
      ∑ a, massEntropy (fun w ↦ (x a w : ℝ)) := by sorry
