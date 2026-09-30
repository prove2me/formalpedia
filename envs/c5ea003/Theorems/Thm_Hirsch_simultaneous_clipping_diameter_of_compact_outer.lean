-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clipping_diameter_of_compact_outer
-- name    : Hirsch.simultaneous_clipping_diameter_of_compact_outer
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T14:11:32.624053+00:00
-- url     : https://prove2.me/theorems/75d26f37-e0bd-4d73-9128-688fe7d5a80c
-- title:
--   Simultaneous clipping diameter from final cut-face budgets
-- statement:
--   Let Q be a compact convex set in finite-dimensional Euclidean space with padded graph diameter at most D. Intersect Q simultaneously with a finite family of halfspaces. If, for every added inequality i, the corresponding exposed face of the final intersection has intrinsic padded graph diameter at most B_i, then the final intersection has padded graph diameter at most D + sum_i B_i. The endpoints may be vertices created by the cuts. The face budgets are for the final intersection, not for intermediate one-cut polytopes.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work PR #53 commit 446304d56513437aad9c0a02fc1d202e41783259, Actions run 34485975796.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clipping_diameter_of_compact_outer
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by sorry

end Hirsch
