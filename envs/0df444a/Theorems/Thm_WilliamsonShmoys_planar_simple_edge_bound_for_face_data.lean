-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_for_face_data
-- name    : WilliamsonShmoys.planar_simple_edge_bound_for_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:36:50.974499+00:00
-- url     : https://prove2.me/theorems/d2873200-f497-4c95-b562-0dee8a72d1d9
-- title:
--   Face-count edge bound for a connected planar drawing
-- statement:
--   A connected finite simple planar graph with at least three vertices satisfies the planar edge bound, expressed without truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_edge_bound_for_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
