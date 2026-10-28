-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:02:59.081572+00:00
-- url     : https://prove2.me/theorems/dceddaa0-1433-40a9-a1bd-b4a6bb21d6b3
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs. A proof chooses a candidate with maximum edge count among the finitely many graphs on V; the original graph ensures the candidate set is nonempty. This step does not need a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_54a0e51c_08bc_41d0_9e00_f8ba78b35c82
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
