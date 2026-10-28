-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1
-- name    : WilliamsonShmoys.planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:05:15.864292+00:00
-- url     : https://prove2.me/theorems/b713f078-5664-4fa1-8fbb-c01b75fa1e9e
-- title:
--   Planar supergraph completion with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    exists H : SimpleGraph V,
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
