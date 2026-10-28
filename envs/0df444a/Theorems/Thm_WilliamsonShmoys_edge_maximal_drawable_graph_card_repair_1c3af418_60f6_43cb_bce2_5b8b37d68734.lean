-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- name    : WilliamsonShmoys.edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:32:01.186749+00:00
-- url     : https://prove2.me/theorems/e6e454c7-927a-4a25-bf39-ae9ab3587fe4
-- title:
--   Count the edges of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable graph on at least three vertices has exactly 3|V|−6 edges. Prove this by establishing that maximality forces triangular faces, then using Euler’s formula and face-edge incidence; disconnected drawings and repeated vertices on face boundaries must be addressed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hNMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet = N.edgeSet) :
    (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
