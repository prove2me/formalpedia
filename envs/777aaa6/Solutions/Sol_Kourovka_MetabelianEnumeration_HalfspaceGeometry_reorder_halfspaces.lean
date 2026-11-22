-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:00.800009+00:00
-- url     : https://prove2.me/submissions/346b947b-4139-48e2-8db2-4c9592d8521d

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_reorder_within

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
theorem _root_.solution (f : X → ℝ) (D μ : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hD0 : 0 ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ ys : List X, ys.Perm xs ∧
      Within f (min 0 (xs.map f).sum) (max μ (xs.map f).sum) 0 ys := by
  apply reorder_within f D _ _ 0 xs hD
  · have hl : min 0 (xs.map f).sum ≤ 0 := min_le_left _ _
    have hu : μ ≤ max μ (xs.map f).sum := le_max_left _ _
    linarith
  · constructor
    · exact min_le_left _ _
    · exact (by linarith : 0 ≤ μ).trans (le_max_left _ _)
  · simpa only [zero_add] using
      And.intro (min_le_right 0 (xs.map f).sum) (le_max_right μ (xs.map f).sum)
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
