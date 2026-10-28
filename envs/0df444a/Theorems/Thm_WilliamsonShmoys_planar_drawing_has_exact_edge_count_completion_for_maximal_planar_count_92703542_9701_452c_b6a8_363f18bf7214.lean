-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:34:50.129987+00:00
-- url     : https://prove2.me/theorems/025e7f85-0cc2-4b5e-afe5-f8abaf4d3fcf
-- title:
--   Drawable graph has an exact edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. Choose an inclusion-maximal drawable supergraph; maximality forces connectedness and triangular faces, and Euler's formula with face-edge incidence counting gives the count. For |V|=3, the completion is the triangle. This removes the planar edge-counting and completion work from the parent; the remaining core obligation is formalizing maximal planar drawings, their faces, and Euler counting for the arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) : exists K : SimpleGraph V, H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
