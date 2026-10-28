-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_edge_augmentation_7f31c9a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_for_edge_augmentation_7f31c9a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:20:51.375472+00:00
-- url     : https://prove2.me/theorems/00123a3c-98e7-4548-b0e7-f4e835072213
-- title:
--   Planar triangulation completion for edge augmentation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type attaining the planar triangulation edge count. This removes the geometric completion and edge-count work from the parent. The three-vertex boundary case is covered: the completion can be the triangle. A proof route is to extend the drawing to a maximal planar graph by adding noncrossing edges within faces, then establish the triangulation edge count using Euler’s formula. The supplied local definition specifies the drawing predicate, but the completion argument remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_for_edge_augmentation_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
