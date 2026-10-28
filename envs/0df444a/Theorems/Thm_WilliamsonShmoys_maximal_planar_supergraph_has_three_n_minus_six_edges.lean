-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_three_n_minus_six_edges
-- name    : WilliamsonShmoys.maximal_planar_supergraph_has_three_n_minus_six_edges
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:10:11.428509+00:00
-- url     : https://prove2.me/theorems/b120a15b-ec4d-4aab-90f2-8639921f1255
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal graph with a planar drawing on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_has_three_n_minus_six_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
