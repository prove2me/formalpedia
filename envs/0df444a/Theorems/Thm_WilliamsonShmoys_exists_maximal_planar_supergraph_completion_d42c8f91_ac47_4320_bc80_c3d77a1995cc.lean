-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:50:26.146235+00:00
-- url     : https://prove2.me/theorems/8fd40662-82f8-4c5c-9d4e-c2ec9eb7a509
-- title:
--   Existence of an inclusion-maximal drawable supergraph for completion
-- statement:
--   A finite drawable graph with at least three vertices has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
