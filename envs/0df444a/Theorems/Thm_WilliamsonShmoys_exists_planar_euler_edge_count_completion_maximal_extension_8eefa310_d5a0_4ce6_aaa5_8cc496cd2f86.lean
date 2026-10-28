-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_euler_edge_count_completion_maximal_extension_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
-- name    : WilliamsonShmoys.exists_planar_euler_edge_count_completion_maximal_extension_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:13:22.239668+00:00
-- url     : https://prove2.me/theorems/d8a3510c-bf70-40c8-b9b5-e30e20e0e2f0
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex type that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_euler_edge_count_completion_maximal_extension_8eefa310_d5a0_4ce6_aaa5_8cc496cd2f86
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by sorry
