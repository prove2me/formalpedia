-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clip_diameter_from_pointed_finite_hpoly
-- name    : Hirsch.simultaneous_clip_diameter_from_pointed_finite_hpoly
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T15:01:56.428304+00:00
-- url     : https://prove2.me/theorems/69b76fc7-5e26-4e4d-b029-1063215825cb
-- title:
--   Simultaneous clipping diameter bound for a pointed finite H-polyhedron
-- statement:
--   Let Q be a nonempty finite H-polyhedron in Euclidean space which contains no affine line. Suppose its old vertex-edge graph has padded diameter at most D. Intersect Q with finitely many additional linear halfspaces, and assume the final clipped set is compact. If the face where added inequality i is tight has intrinsic graph diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. The proof derives the no-common-row-kernel characterization of pointedness, proves the old H-vertex set is finite, chooses a canonical summed-normal far cap internally, classifies every new cap vertex as a horizon vertex adjacent to an old vertex, and applies the verified strict-centre-free exterior clipping transfer.
-- source:
--   Kernel-verified pointed finite-H-polyhedron cap construction and clipping transfer in jjoshua2/prove2me-work.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clip_diameter_from_pointed_finite_hpoly
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty)
    (hpointed : ¬ ∃ x r : EuclideanSpace ℝ (Fin d),
      r ≠ 0 ∧ ∀ t : ℝ, x + t • r ∈ Hpoly a b)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hPc : IsCompact (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE
      ((Hpoly a b ∩ {y | ∀ j, f j y ≤ c j}) ∩ {x | f i x = c i}) (B i)) :
    DiamLE (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}) (D + 1 + ∑ i, B i) := by sorry

end Hirsch
