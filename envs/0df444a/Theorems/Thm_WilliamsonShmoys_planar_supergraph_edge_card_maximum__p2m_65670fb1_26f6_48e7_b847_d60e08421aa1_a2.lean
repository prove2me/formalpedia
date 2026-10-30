-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- name    : WilliamsonShmoys.planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:54:50.503393+00:00
-- url     : https://prove2.me/theorems/14e5a5b6-f5c8-41dc-9ffe-e2b4f22f7e7c
-- title:
--   Maximum edge count among planar supergraphs
-- statement:
--   For a finite ordered vertex type, there is a planar supergraph of any planar graph whose edge count is at least that of every other planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
