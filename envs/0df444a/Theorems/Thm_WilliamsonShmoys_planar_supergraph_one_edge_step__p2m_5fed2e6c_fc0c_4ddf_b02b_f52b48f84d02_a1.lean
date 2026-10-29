-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
-- name    : WilliamsonShmoys.planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:17:18.775823+00:00
-- url     : https://prove2.me/theorems/f3c47a63-e0db-468e-855d-93d2c2950018
-- title:
--   Take one edge from a drawable supergraph
-- statement:
--   If a drawable graph strictly contains another graph on the same finite vertex type, the smaller graph has a drawable one-edge extension. Choose an edge in the set difference and restrict the larger graph's drawing to the smaller graph plus that edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hSub : G.edgeSet ⊆ K.edgeSet)
    (hStrict : G.edgeSet.ncard < K.edgeSet.ncard)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
