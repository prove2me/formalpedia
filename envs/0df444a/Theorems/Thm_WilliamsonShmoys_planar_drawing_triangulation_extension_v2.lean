-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_v2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:17:31.392401+00:00
-- url     : https://prove2.me/theorems/289ce3bb-0db0-49c7-a580-3ed9606104c8
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing can be extended on the same vertex set to a crossing-free simple graph containing all its edges and attaining the triangulated planar edge count. The child removes the topological augmentation and planar Euler-counting work from the parent; the parent only uses edge-count monotonicity and linear arithmetic. A proof can add noncrossing edges within faces until the embedding is maximal, show maximality forces triangular faces, and count edges using Euler’s formula. The key remaining obligation is formalizing this route for the given drawing predicate, including disconnected starting graphs and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
