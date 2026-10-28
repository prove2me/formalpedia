-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:54:40.922153+00:00
-- url     : https://prove2.me/theorems/e17f42cd-7973-43e2-99de-b184c28d5046
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal by edge-set inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by sorry
