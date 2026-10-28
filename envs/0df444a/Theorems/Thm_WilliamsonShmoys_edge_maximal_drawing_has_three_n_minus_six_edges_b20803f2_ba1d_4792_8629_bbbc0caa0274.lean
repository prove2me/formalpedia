-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- name    : WilliamsonShmoys.edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:29:57.667555+00:00
-- url     : https://prove2.me/theorems/4c29d803-dc21-4f24-8d2c-ce4e8908d2d3
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
