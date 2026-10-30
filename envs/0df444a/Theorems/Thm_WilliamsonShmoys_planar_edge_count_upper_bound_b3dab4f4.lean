-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b3dab4f4
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_b3dab4f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:30:44.968823+00:00
-- url     : https://prove2.me/theorems/d2dd9324-4b77-4cc3-a1ac-0cf2fc14afcd
-- title:
--   Euler edge upper bound for a drawable finite simple graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The proof route is Euler's formula together with the lower bound of three on each face boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_b3dab4f4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
