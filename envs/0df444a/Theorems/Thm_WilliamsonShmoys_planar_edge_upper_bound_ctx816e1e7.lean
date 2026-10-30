-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ctx816e1e7
-- name    : WilliamsonShmoys.planar_edge_upper_bound_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:34:54.588537+00:00
-- url     : https://prove2.me/theorems/834ddcb8-c061-42f9-8623-a09c413b4215
-- title:
--   Planar edge upper bound for this target
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
