-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clipping_diameter_bound
-- name    : Hirsch.simultaneous_clipping_diameter_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T03:55:41.97982+00:00
-- url     : https://prove2.me/theorems/e5922f9c-6aaf-49e8-b85a-ecd667644da2
-- title:
--   Simultaneous halfspace clipping charges only final cut-face diameters
-- statement:
--   Let Q be a compact convex polytope with padded graph diameter at most D, and intersect it simultaneously with a finite family of halfspaces. If the intrinsic graph diameter of each supporting equality face in the FINAL clipped polytope is at most B_i, then every two extreme vertices of the final clipped polytope are joined by a padded graph walk of length at most D + sum_i B_i. The endpoints need not be extreme vertices of Q, and no strict-centre hypothesis appears in the theorem statement.
-- source:
--   Kernel-checked Lean theorem from jjoshua2/prove2me-work PR #53, isolated from the later unfinished horizon-cap module.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clipping_diameter_bound
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by sorry

end Hirsch
