-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_target_4b205fd4_maximal_faces_euler_incidence
-- name    : WilliamsonShmoys.planar_edge_count_target_4b205fd4_maximal_faces_euler_incidence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:05:16.803371+00:00
-- url     : https://prove2.me/theorems/30b929a6-11eb-4f1a-9a47-89391e3d4175
-- title:
--   Euler and incidence equations for maximal drawable graphs
-- statement:
--   A drawable simple graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has a face count satisfying Euler's equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_target_4b205fd4_maximal_faces_euler_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
