-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:24.38909+00:00
-- url     : https://prove2.me/theorems/91b0396d-b61c-4659-90f8-b13543ceeb7a
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   A graph with the supplied planar drawing witness that is maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V|−6 edges. The proof route is to show maximality forces a triangulation, then count edges via Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_lower__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K)
    (hKMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
