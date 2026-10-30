-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1
-- name    : WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:53:12.252244+00:00
-- url     : https://prove2.me/theorems/bee4d76c-e86b-4fb5-809f-021321304750
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices can be extended on the same vertex set to a crossing-free triangulation with exactly three times the number of vertices minus six edges. This removes the planar augmentation and edge-count step from the parent; maximality then forces the extension to equal the original graph. An independent proof route is to augment a finite planar embedding until every face is triangular and apply Euler’s formula. The remaining core obligation is formalizing that augmentation and edge-count argument for the supplied continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_6ce17d90_7e34_4ced_9818_f205b3115d6a_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
