-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:45:15.989009+00:00
-- url     : https://prove2.me/theorems/536aaf66-0a7c-4c8d-b8d1-73a7e039d5bd
-- title:
--   Edge count of a maximal planar drawing for completion
-- statement:
--   A graph on at least three vertices that admits the specified crossing-free drawing and has no drawing-admitting strict supergraph has exactly 3|V| − 6 edges. This follows by converting the drawing to a planar embedding, showing maximality forces a connected triangulation, and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion__p2m_437ae037_6315_4598_a71b_f3c87f44dd3b_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊂ K.edgeSet → False)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
