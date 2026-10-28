-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_drawing_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_drawing_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:49:42.936543+00:00
-- url     : https://prove2.me/theorems/8a11d77e-8792-4d46-b189-4df3a0822f7e
-- title:
--   Edge count of a maximal planar drawing graph for the drawing edge bound
-- statement:
--   A simple graph on at least three vertices that is maximal under edge inclusion among graphs admitting this planar drawing predicate has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHdraw : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
