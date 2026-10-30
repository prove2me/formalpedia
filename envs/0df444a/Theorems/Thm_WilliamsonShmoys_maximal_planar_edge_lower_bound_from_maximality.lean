-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_from_maximality
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_from_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:29:58.385145+00:00
-- url     : https://prove2.me/theorems/eb003b3d-a492-4a49-92ea-fad95e296393
-- title:
--   Maximal drawable graphs have at least 3n − 6 edges
-- statement:
--   A maximal graph with a crossing-free drawing and at least three vertices has at least 3n − 6 edges; maximality forces a triangulation, and Euler’s formula gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_from_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
