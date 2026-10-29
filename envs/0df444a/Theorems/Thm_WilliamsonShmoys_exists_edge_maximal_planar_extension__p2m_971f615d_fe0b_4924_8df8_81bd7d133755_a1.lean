-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:05:55.838986+00:00
-- url     : https://prove2.me/theorems/4cdb185e-0a6c-484e-89d8-c7c1ecef4e42
-- title:
--   Existence of an edge-maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same finite vertex type that admits no strictly larger drawable supergraph on that type. The proof route is finite maximization over edge sets, retaining a drawing witness for each candidate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
