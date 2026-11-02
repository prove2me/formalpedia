-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:42.765715+00:00
-- url     : https://prove2.me/theorems/c5a41056-5cba-4140-8251-f29430518514
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph on a finite linearly ordered vertex type with at least three vertices, a drawing of the specified kind, and no proper planar supergraph on that type has exactly 3n - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hKDrawing : HasPlanarDrawingOn K)
    (hKMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
