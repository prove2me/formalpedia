-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:48.177754+00:00
-- url     : https://prove2.me/theorems/6b45552a-e614-43a1-bcb2-5a02dc98d5fe
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3 * |V| - 6` edges. Maximality forces connectedness and triangular faces; Euler’s formula and counting face-edge incidences yield the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hMax : ∀ H' : SimpleGraph V, H ≤ H' → H' ≠ H → ¬ HasPlanarDrawingOn H') (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
