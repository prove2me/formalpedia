-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:39:18.104982+00:00
-- url     : https://prove2.me/theorems/54a0e51c-08bc-41d0-9e00-f8ba78b35c82
-- title:
--   Completion of a planar drawing to a triangulation
-- statement:
--   Every finite graph drawable under the supplied definition, on at least three vertices, has a drawable spanning supergraph with exactly three times the vertex count minus six edges. This removes the geometric augmentation and Euler-count work from the parent. Independently, one can convert the given finite drawing to a plane embedding, add edges across components and within faces until the embedding is a triangulation, then use Euler’s formula and count three edge-sides per face. For three vertices the completion is the triangle; disconnected inputs and isolated vertices are handled by the augmentation. The remaining core is formalizing this augmentation and triangulation argument for the supplied continuous-arc definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
