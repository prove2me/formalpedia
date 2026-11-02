-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:50.989477+00:00
-- url     : https://prove2.me/theorems/8d2492c2-a620-4e30-8a73-7621e3b1e96d
-- title:
--   Maximal drawable graphs have the planar Euler edge count
-- statement:
--   If a drawable simple graph on at least three finite ordered vertices has no strictly larger drawable supergraph on those vertices, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      letI : DecidableRel L.Adj := Classical.decRel L.Adj
      K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
