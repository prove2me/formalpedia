-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:48:55.165594+00:00
-- url     : https://prove2.me/theorems/41b75d1a-edfd-4ff1-ab5e-5b5b9010771e
-- title:
--   An edge-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices with no drawable proper supergraph on the same vertex type has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
