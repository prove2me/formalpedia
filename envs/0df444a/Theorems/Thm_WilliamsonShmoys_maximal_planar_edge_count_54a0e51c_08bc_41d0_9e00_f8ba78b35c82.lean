-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- name    : WilliamsonShmoys.maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:10:16.382629+00:00
-- url     : https://prove2.me/theorems/ebdbae72-2386-4432-8f10-b20acab57c4b
-- title:
--   Edge count of a maximal graph under the supplied planar drawing predicate
-- statement:
--   An inclusion-maximal graph drawable under the supplied continuous-arc predicate, on at least three vertices, has exactly three times the vertex count minus six edges. The proof converts the arc drawing into a plane embedding, shows maximality forces a connected triangulation, and applies Euler’s formula with face-edge incidence counting. The lower bound preserves the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
