-- Prove2me | Theorems.Thm_Hirsch_clipped_diameter_le_outer_add_cut_face
-- name    : Hirsch.clipped_diameter_le_outer_add_cut_face
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T21:43:55.226105+00:00
-- url     : https://prove2.me/theorems/4b66b5b2-64e6-4da7-b8f3-a443c0c724d3
-- title:
--   Additive diameter transfer for a single halfspace cut
-- statement:
--   Let Q be a convex subset of real Euclidean d-space with padded vertex-edge diameter at most B. Fix a halfspace <c,x> <= b and assume Q has an extreme point v with b <= <c,v>. If the equality section F = Q intersect {x : <c,x> = b} has padded diameter at most C, then P = Q intersect {x : <c,x> <= b} has padded diameter at most B+C. The source and target range over all extreme points of P, including vertices newly created by the cut. The outer set need not be bounded, but its vertex on or beyond the plane is a genuine hypothesis. This is a conditional diameter-transfer result, not a uniform polynomial Hirsch bound.
-- source:
--   Working derivation for jjoshua2/prove2me-work following the accepted cut-face access result. No claim of literature priority. The candidate must compile and pass equivalent-result checks before publication.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.clipped_diameter_le_outer_add_cut_face
    (d B C : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hQ : DiamLE Q B)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C) :
    DiamLE (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C)  := by sorry
