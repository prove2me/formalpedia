-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_extension_exists_bcd4e9c3
-- name    : WilliamsonShmoys.planar_completion_maximal_extension_exists_bcd4e9c3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:53:25.123651+00:00
-- url     : https://prove2.me/theorems/054b34b1-1a5e-4637-8d35-6f0e01917ca8
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph with no proper drawable supergraph on that type. Choose a maximal edge set among the finitely many supergraphs that have a drawing; any drawable supergraph of the chosen graph must have the same edge set and thus be equal to it. This needs no lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_maximal_extension_exists_bcd4e9c3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
