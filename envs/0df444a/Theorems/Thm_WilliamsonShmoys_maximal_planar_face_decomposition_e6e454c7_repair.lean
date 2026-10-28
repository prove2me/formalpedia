-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_e6e454c7_repair
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_e6e454c7_repair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T08:10:54.969304+00:00
-- url     : https://prove2.me/theorems/4e5213d4-3311-4131-b1b0-93796a306a5d
-- title:
--   Euler and triangular face-incidence equations for maximal planar drawings
-- statement:
--   For a drawable edge-maximal simple graph with at least three vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation. This removes the topological and counting work from the parent. A proof can turn the drawing into a plane embedding, use maximality to establish connectedness and triangular faces, and apply Euler’s formula and incidence counting. The condition of at least three vertices is essential to these equations; it includes the boundary case of exactly three vertices, whose maximal graph is a triangle. The remaining core obligation is formalizing the embedding argument, especially the exclusion of repeated facial boundary structure, from the given drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_e6e454c7_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPMax : ∀ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      P.edgeSet ⊆ Q.edgeSet → Q.edgeSet = P.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = P.edgeSet.ncard + 2 ∧
      3 * f = 2 * P.edgeSet.ncard := by sorry
