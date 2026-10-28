-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_completion_maximal_extension_6e15fe35
-- name    : WilliamsonShmoys.triangulation_completion_maximal_extension_6e15fe35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:17:39.418326+00:00
-- url     : https://prove2.me/theorems/e69da030-f88d-418d-85ef-4952feacaea1
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Every drawable graph on a fixed finite vertex type has an inclusion-maximal drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_completion_maximal_extension_6e15fe35
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N := by sorry
