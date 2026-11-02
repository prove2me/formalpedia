-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:39.47103+00:00
-- url     : https://prove2.me/theorems/6df3e4cc-9852-43e8-a059-d1d510a4cce9
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every graph with the supplied crossing-free drawing witness and at least three vertices has at most 3|V|−6 edges. This is the Euler edge bound for a simple planar graph; connectedness is not assumed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_upper__p2m_c5a41056_5cba_4140_8251_f29430518514_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
