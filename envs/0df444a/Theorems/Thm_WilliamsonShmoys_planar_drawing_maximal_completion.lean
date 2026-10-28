-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion
-- name    : WilliamsonShmoys.planar_drawing_maximal_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:42:28.988833+00:00
-- url     : https://prove2.me/theorems/b7145e12-09ad-4628-8ddf-1065b8a2bcd7
-- title:
--   Maximal planar completion of a finite drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free arc drawing has a crossing-free simple supergraph on the same vertices whose edge count is exactly 3|V|−6, and the original graph’s edge count is no larger. For |V|=3 this is the triangle; for larger vertex sets the completion is a triangulation. The proof uses maximal planar augmentation and Euler’s formula. This removes the principal topological and counting work from the parent theorem; the remaining obligation is to formalize that augmentation for the exact arc-drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
