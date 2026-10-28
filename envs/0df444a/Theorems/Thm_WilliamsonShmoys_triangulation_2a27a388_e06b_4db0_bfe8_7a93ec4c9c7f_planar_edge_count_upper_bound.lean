-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
-- name    : WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:20:55.577747+00:00
-- url     : https://prove2.me/theorems/610126f0-5c66-41f3-b764-5caf7bf992b8
-- title:
--   Planar edge count upper bound
-- statement:
--   Any graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler-formula upper bound for simple planar graphs. A proof route is to establish the bound for connected embeddings, then handle disconnected graphs by joining components through drawable edges or applying the component bounds and the vertex-count condition. The restriction |V|≥3 is retained; tiny graphs are not covered by this formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_planar_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
