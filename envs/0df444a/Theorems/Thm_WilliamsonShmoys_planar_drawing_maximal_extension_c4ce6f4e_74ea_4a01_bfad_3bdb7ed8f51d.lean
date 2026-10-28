-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:39:53.246887+00:00
-- url     : https://prove2.me/theorems/1179d29c-69b0-40a1-afd6-17180844ca72
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      W ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) ∧
      W.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
