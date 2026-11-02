-- Prove2me | Theorems.Thm_planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
-- name    : planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:34:44.406587+00:00
-- url     : https://prove2.me/theorems/1c8b27b7-8819-4f33-a2b4-5f43f0f6ed4e
-- title:
--   Drawable completion with the triangulation edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3n−6 edges. The extension preserves the original edges; the conclusion uses the stated drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem planar_drawing_completion_edge_count__p2m_f1fd84d6_ec35_411e_9342_50b2daa0def2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
