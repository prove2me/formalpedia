-- Prove2me | Theorems.Thm_Hirsch_zonotope_all_endpoint_original_routes
-- name    : Hirsch.zonotope_all_endpoint_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-20T11:57:31.263971+00:00
-- url     : https://prove2.me/theorems/26dac93f-73ea-405f-9597-11a05db6f697
-- title:
--   Original-edge routes between arbitrary zonotope vertices without supplied objectives
-- statement:
--   For all natural d and m and any family of m real generators in R^d, any two actual extreme points u and v of the ORIGINAL coefficient segment sum can be joined by a walk of at most m nondegenerate original exposed edges. Every visited point is extreme in the same original body; every consecutive whole closed segment is IsExposed and IsExtreme there. No exposing objectives, regularity, vertex catalogue, Boolean injectivity, face/edge oracle or short route is supplied. The proof derives regular exposing objectives for arbitrary requested extreme points, then reuses the accepted ordered sweep route. Zero, parallel, opposite, repeated and rank-deficient generators, d=0, m=0 and equal endpoints are included. The count m is presented generators, not original H facets. The statement does not provide a polynomial original-facet generator budget, a shortest path, an extracted algorithm or a solution of unrestricted Polynomial Hirsch.
-- source:
--   Full endpoint applicability after accepted #315, theorem58ae59bf-f663-4bbb-ba6b-1858d7a64009, accepted proofba5f8fbc6f1d49412a619a97412dba002e731826. Its complete1048-line namespace prefix is reused byte-for-byte, excluding the old standalone solution/prints. New finite Boolean corner hull identification, strict separation of an extreme point from the hull of the other images, and saturation/toggle argument construct regular exposing objectives. Uses pinned Mathlib parallelepiped_eq_convexHull, finite convex-hull closedness, extreme convex deletion and geometric_hahn_banach_closed_point. This formalizes a classical zonotope bound and makes no historical-priority or improved best-bound claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_all_endpoint_original_routes (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (u v : Fin d → ℝ) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i) = x}
    u ∈ Z.extremePoints ℝ → v ∈ Z.extremePoints ℝ →
      ∃ L : ℕ, L ≤ m ∧ ∃ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u ∧ p (Fin.last L) = v ∧ (∀ i, p i ∈ Z.extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) ∧
          IsExtreme ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
