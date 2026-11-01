-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:29.447519+00:00
-- url     : https://prove2.me/theorems/f2cfae8b-743a-4350-8c03-fa33aa7b455e
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8b952692_ce82_4b1a_b285_daef0e717378_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) (hcard : 3 ≤ Fintype.card V) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
