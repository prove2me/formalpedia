-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion_437ae037_6315_4598_a71b_f3c87f44dd3b
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_437ae037_6315_4598_a71b_f3c87f44dd3b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:30:19.853148+00:00
-- url     : https://prove2.me/theorems/1e7de999-0dd6-476b-82d1-ec00a558b77b
-- title:
--   Edge count of a maximal planar drawing for completion
-- statement:
--   A graph admitting a planar drawing and having no drawing-admitting strict supergraph has exactly 3|V|−6 edges when |V| ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_437ae037_6315_4598_a71b_f3c87f44dd3b
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊂ K.edgeSet → False)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
