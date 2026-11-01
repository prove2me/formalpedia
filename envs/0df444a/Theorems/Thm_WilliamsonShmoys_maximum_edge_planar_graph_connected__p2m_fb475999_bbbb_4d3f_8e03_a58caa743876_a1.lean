-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- name    : WilliamsonShmoys.maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:21.502413+00:00
-- url     : https://prove2.me/theorems/5d6c09bb-0ad5-47bc-b88e-37408079b780
-- title:
--   A maximum-edge drawable graph is connected
-- statement:
--   A drawable graph on at least two vertices that maximizes edge count among drawable graphs on the same vertex set is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj)
    (hcard : 2 ≤ Fintype.card V)
    (hQ : HasPlanarDrawingOn Q)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K →
      (letI : DecidableRel Q.Adj := dQ
       letI : DecidableRel K.Adj := dK
       Q.edgeFinset.card ≤ K.edgeFinset.card)) :
    Q.Connected := by sorry
