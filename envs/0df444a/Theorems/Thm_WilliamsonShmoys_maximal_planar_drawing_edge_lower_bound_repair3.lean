-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_repair3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:51:47.143753+00:00
-- url     : https://prove2.me/theorems/b722b978-1cbe-4a20-9a11-dde6ad40cbbf
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal under edge inclusion among drawable graphs has at least `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHdraw : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
