-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:32:41.549334+00:00
-- url     : https://prove2.me/theorems/8895f479-77a0-4c1e-903f-b3af7ab1e8bd
-- title:
--   A planar graph has a triangulated completion on the same vertices
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This supplies a completion whose edge count can be compared with the disconnected graph’s bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
