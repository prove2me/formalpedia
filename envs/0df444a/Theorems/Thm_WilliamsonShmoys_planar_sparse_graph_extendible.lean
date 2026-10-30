-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_extendible
-- name    : WilliamsonShmoys.planar_sparse_graph_extendible
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:03:07.46938+00:00
-- url     : https://prove2.me/theorems/29a0a249-4f45-414d-988d-37d4a93ff923
-- title:
--   Sparse drawable graphs admit a strict drawable extension
-- statement:
--   Any drawable simple graph on at least three vertices with fewer than 3|V|−6 edges has a drawable supergraph on the same vertices that strictly adds an edge. The strict inequality handles the boundary: graphs at the 3|V|−6 threshold are not covered.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_sparse_graph_extendible
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K.edgeSet ⊆ H.edgeSet := by sorry
