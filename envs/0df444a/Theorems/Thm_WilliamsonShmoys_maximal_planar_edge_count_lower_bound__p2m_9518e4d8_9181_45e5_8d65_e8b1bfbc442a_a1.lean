-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:23.534595+00:00
-- url     : https://prove2.me/theorems/61543ccf-c10c-45ac-85dc-db241ebaf64e
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that admits no strictly larger drawable simple graph on the same vertex set has at least 3|V|−6 edges. A proof route extends the plane drawing to a triangulation by adding edges, then uses maximality to identify the extension with the original graph and applies Euler’s face count. The argument must handle disconnected drawings and preserve the fixed vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall K : SimpleGraph V, G <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  sorry
