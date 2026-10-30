-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_from_embedding
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_from_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:45:33.883826+00:00
-- url     : https://prove2.me/theorems/35554814-b744-4046-ad44-5d0d6f608b9b
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3|V| − 6` edges. Prove this by establishing that maximality forces a triangulation, then use Euler's formula and face-edge incidence counting; treat the three-vertex triangle boundary case explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_from_embedding
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      P.edgeSet ⊆ Q.edgeSet → Q.edgeSet ⊆ P.edgeSet) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
