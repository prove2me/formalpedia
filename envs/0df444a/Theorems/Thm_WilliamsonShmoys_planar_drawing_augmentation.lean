-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation
-- name    : WilliamsonShmoys.planar_drawing_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:59:18.180242+00:00
-- url     : https://prove2.me/theorems/9835eb2f-0298-4fa3-b4ee-8255acaa7a45
-- title:
--   Augment a planar drawing to a maximal planar supergraph
-- statement:
--   Any finite simple graph with at least three vertices and the given crossing-free drawing has a planar supergraph on the same vertices whose edge count is exactly 3n − 6. The strict vertex lower bound preserves the triangulation boundary case n = 3. A proof route is to connect components and add noncrossing edges until the embedding is maximal; maximality yields triangular faces, and Euler’s formula gives the count. This removes the geometric and Euler argument from the parent, which only needs edge-count monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
