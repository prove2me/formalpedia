-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_completion_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:19:08.065582+00:00
-- url     : https://prove2.me/theorems/8b03e490-4bd8-4fa5-8f79-8c509d334de3
-- title:
--   A drawable graph has a maximal drawable completion
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_completion_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
