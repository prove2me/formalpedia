-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:46.435341+00:00
-- url     : https://prove2.me/theorems/f8e496dc-ac86-4dbf-b6d9-446222a8ec24
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V| − 6 edges. Prove this by showing a maximal planar drawing is connected with triangular faces, then combining Euler’s formula with face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hNdraw : HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, LE.le N K -> HasPlanarDrawingOn K -> K = N) :
    3 * Fintype.card V =
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card) + 6 := by sorry
