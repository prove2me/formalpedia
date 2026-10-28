-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:35:28.392091+00:00
-- url     : https://prove2.me/theorems/c780a60d-2eaa-4bd7-835f-c8066a29786f
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ M : SimpleGraph V,
        Q ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M ≤ Q := by sorry
