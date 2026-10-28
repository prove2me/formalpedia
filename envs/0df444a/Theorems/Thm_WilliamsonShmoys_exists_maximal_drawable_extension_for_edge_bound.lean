-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension_for_edge_bound
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:35:53.939096+00:00
-- url     : https://prove2.me/theorems/0c8d9cb8-a074-494e-9cb2-7ac0daf65d84
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set with no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_extension_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  sorry
