-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:59.373799+00:00
-- url     : https://prove2.me/theorems/10767c1e-3761-455c-b81d-2c159386481f
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that is inclusion-maximal among drawable supergraphs has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
