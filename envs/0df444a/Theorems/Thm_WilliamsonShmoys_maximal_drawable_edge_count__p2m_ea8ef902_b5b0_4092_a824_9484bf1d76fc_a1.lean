-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:32.972194+00:00
-- url     : https://prove2.me/theorems/53978d9a-ff21-4c38-b5ef-6e6d6a6a4bf9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly `3 * |V| - 6` edges. The proof route is to establish that maximality forces a triangulation, then combine Euler's formula with face-edge incidence counting; the three-vertex case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hKdraw : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> L = K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry
