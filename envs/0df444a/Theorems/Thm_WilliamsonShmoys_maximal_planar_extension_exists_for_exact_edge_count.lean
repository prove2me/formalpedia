-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists_for_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_extension_exists_for_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:36:45.619196+00:00
-- url     : https://prove2.me/theorems/2f5b2b56-2eb9-44b2-bf80-353916fb4e6c
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph on the same vertices with no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists_for_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
