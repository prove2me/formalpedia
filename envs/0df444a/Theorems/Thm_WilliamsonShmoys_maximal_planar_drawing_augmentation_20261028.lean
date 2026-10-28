-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_augmentation_20261028
-- name    : WilliamsonShmoys.maximal_planar_drawing_augmentation_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:11:52.627229+00:00
-- url     : https://prove2.me/theorems/8910f512-7976-4436-9325-0e9b3d81be64
-- title:
--   Augment a planar drawing to a maximal planar graph
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing on those vertices, there is a drawable supergraph on the same vertices with exactly 3|V|−6 edges. Its role is to supply the planar augmentation and edge count; applying the parent’s maximality hypothesis identifies this supergraph with the original graph. A proof route is to triangulate the finite planar embedding without adding vertices and use Euler’s formula to count edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_augmentation_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
