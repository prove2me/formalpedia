-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:48.103965+00:00
-- url     : https://prove2.me/theorems/db2bc25d-3c02-46be-91b6-cd4d6f11e2cd
-- title:
--   Planar drawing augmentation to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on a finite, linearly ordered vertex set of size at least three is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. This is the standard augmentation-to-a-triangulation result, specialized to HasPlanarDrawingOn. The parent applies maximality to the resulting R to obtain R ≤ G; together with G ≤ R, equality transfers the stated edge count to G. A proof route is to extend the drawing to a maximal planar embedding, prove each face is triangular, and count face-edge incidences using Euler’s formula. For |V|=3 the maximal augmentation is K3, so the edge count is 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_2ea99569_5736_493f_8895_a821efa27469_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ R : SimpleGraph V, G <= R ∧ HasPlanarDrawingOn R ∧
      (letI : DecidableRel R.Adj := Classical.decRel R.Adj
       3 * Fintype.card V = R.edgeFinset.card + 6) := by sorry
