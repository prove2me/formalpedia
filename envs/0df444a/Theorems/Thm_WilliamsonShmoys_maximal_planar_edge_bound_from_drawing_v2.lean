-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_from_drawing_v2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_from_drawing_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:30:48.559339+00:00
-- url     : https://prove2.me/theorems/9ff447b0-5b39-4936-adc9-9e8acd988fb2
-- title:
--   Edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal simple graph admitting the specified planar drawing, on at least three vertices, has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound_from_drawing_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hmax : ∀ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K = M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
