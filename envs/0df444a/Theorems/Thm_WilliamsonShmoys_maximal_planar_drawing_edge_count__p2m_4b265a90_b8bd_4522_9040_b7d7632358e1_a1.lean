-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:48:29.045804+00:00
-- url     : https://prove2.me/theorems/1bf1e13a-8988-4e3f-82f0-103a93d3cf68
-- title:
--   Edge count of an inclusion maximal planar drawing
-- statement:
--   An inclusion maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
