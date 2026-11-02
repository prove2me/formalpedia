-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_components__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_across_components__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:05.896215+00:00
-- url     : https://prove2.me/theorems/fade06b1-32b8-4a53-aa89-cdc16dd3ccec
-- title:
--   Add a drawable edge between distinct components
-- statement:
--   If two vertices are in different connected components of a finite graph with a crossing-free drawing, one can add the edge between them and retain a crossing-free drawing on the same vertices. This isolates the topological arc-routing step. A proof route is to use the finite embedded drawing and join the two components through complementary regions, making the new arc meet the existing drawing only at its endpoints. Since unreachable vertices cannot already be adjacent, the added edge strictly enlarges the graph. This claim needs a proof for the exact arc-based definition; the cited book proof was not available in sufficient formal detail.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_across_components__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (huv : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
