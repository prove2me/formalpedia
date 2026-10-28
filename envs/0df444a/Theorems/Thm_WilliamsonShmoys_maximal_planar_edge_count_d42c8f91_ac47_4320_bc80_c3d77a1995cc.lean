-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:23:32.225813+00:00
-- url     : https://prove2.me/theorems/b9ab3ea4-7e0e-4c00-98f6-9387c87cc044
-- title:
--   Euler edge count for a maximal simple planar graph
-- statement:
--   An inclusion-maximal simple planar graph on at least three vertices has exactly 3n − 6 edges. This is the Euler-count step: maximality forces a connected triangulation, and Euler’s formula then gives the edge count. The assertion includes the n = 3 case, where the maximal graph is a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
