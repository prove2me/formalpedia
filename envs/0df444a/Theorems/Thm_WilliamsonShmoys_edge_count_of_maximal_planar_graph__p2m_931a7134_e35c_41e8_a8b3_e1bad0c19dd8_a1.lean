-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:06.81607+00:00
-- url     : https://prove2.me/theorems/128ccb5d-2869-4813-8833-a7ab44ab4b11
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly `3n - 6` edges. A proof route is to show maximality forces every face of the embedded graph to be triangular, then combine Euler’s formula with the count of face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hmax : ∀ H : SimpleGraph V, W ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = W) (hV : 3 ≤ Fintype.card V) : W.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
