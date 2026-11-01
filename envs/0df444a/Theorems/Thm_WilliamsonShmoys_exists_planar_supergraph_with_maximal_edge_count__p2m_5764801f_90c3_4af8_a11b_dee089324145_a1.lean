-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:23.007392+00:00
-- url     : https://prove2.me/theorems/d31de1f7-ef50-4693-bbf0-93f59f6d9afd
-- title:
--   Complete a drawable graph to maximum planar edge count
-- statement:
--   Every graph with a planar drawing has a drawable supergraph on the same vertex set whose edge count is the maximum possible planar edge count for that number of vertices. This is the completion step: its geometric proof must extend the drawing, including for disconnected graphs, and handle vertex counts below three separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      K.edgeFinset.card =
        (if Fintype.card V < 3 then (Fintype.card V).choose 2
         else 3 * Fintype.card V - 6) := by sorry
