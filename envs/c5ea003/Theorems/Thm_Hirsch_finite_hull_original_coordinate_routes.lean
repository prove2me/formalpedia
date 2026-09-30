-- Prove2me | Theorems.Thm_Hirsch_finite_hull_original_coordinate_routes
-- name    : Hirsch.finite_hull_original_coordinate_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-21T21:58:47.595769+00:00
-- url     : https://prove2.me/theorems/5a81c2f0-e6fe-4eea-a627-0acdde34206a
-- title:
--   Original polytope edge routes bounded by actual vertex-coordinate levels
-- statement:
--   For any finite set C of real points in ambient dimension d and any two actual extreme points of P=convexHull(C), construct an indexed walk through actual extreme points of P. Every consecutive pair is distinct and its entire segment is an extreme subset of the original P. The length is at most the sum, over the d coordinates, of the number of distinct values attained by ACTUAL vertices minus one. The actual vertex set is obtained by filtering C using Mathlib extremality; its completeness is derived. No neighbor graph, improving-edge witness, face catalogue, connectivity or bounded walk is assumed. C may contain redundant/interior points; nonsimple and lower-dimensional hulls, d=0 and equal endpoints are included. The bound depends on coordinate levels, which need not be polynomial in original facets. This is not Polynomial Hirsch, a shortest-path theorem, a nonrevisiting theorem or an algorithmic polynomial-time claim.
-- source:
--   Classical coordinate-extreme/Kleinschmidt--Onn routing argument, continuing the explicitly missing geometric adapter of accepted PR #283 (Hirsch.finite_coordinate_extreme_route_bound). Reuses its exact proof after renaming only the old public root/print; reuses accepted finite perturbation and segment-endpoint proof bodies from #313/#309 via #320. Generalizes the finite-vertex strict-separation argument used in #316. The new proof constructs improving original exposed edges using normalized contrast regularization, proves full coordinate support-face closure, derives the actual vertex hull from Krein--Milman plus finiteness, and instantiates the accepted finite route theorem. No historical-priority claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.finite_hull_original_coordinate_routes (d : ℕ) (C : Finset (Fin d → ℝ)) (u v : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hv : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
      (fun p => Classical.propDecidable _) C
    ∃ L : ℕ, L ≤ ∑ j : Fin d, ((V.image (fun x => x j)).card-1) ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ i, p i ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExtreme ℝ (convexHull ℝ (C : Set (Fin d → ℝ)))
            (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
