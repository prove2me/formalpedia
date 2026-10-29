-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4
-- name    : WilliamsonShmoys.planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:34:26.011268+00:00
-- url     : https://prove2.me/theorems/5a949825-f81a-4c8d-a9c0-487ac649892b
-- title:
--   Extension of a drawable graph to the planar extremal edge count
-- statement:
--   Every graph drawable on a finite linearly ordered vertex type with at least three vertices extends to a drawable graph on that same vertex type with exactly three times the number of vertices minus six edges. The lower bound of three is preserved, including the triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hDraw : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V, W ≤ X ∧ HasPlanarDrawingOn X ∧
      X.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
