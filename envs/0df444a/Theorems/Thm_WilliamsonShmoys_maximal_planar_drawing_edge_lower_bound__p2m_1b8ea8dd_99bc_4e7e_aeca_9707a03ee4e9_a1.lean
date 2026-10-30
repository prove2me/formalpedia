-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:40:07.164409+00:00
-- url     : https://prove2.me/theorems/0cd4b9a1-dcab-4b06-b6ad-2748a36b5bdf
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3|V|−6` edges. The standard proof shows maximality forces every face to be triangular, then uses Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_1b8ea8dd_99bc_4e7e_aeca_9707a03ee4e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
