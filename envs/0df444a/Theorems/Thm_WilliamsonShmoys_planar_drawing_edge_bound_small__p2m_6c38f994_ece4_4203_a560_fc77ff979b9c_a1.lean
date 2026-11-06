-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_small__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_small__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:23.930831+00:00
-- url     : https://prove2.me/theorems/aa93fc0d-3b8b-4ccf-af3c-fc1fe2554efb
-- title:
--   Simple graph edge bound for at most two vertices
-- statement:
--   For a simple graph on at most two vertices, the edge count is at most n−1, using natural subtraction. The cases n=0 and n=1 have no edges and right-hand side zero; the case n=2 has at most the single possible edge. The drawing hypothesis is unused, making this a reusable small-cardinality fact. A proof route is finite cardinality comparison for the edge set, or explicit cardinality case splits.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_bound_small__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Fintype.card V ≤ 2 →
      M.edgeSet.ncard ≤ Fintype.card V - 1 := by sorry
