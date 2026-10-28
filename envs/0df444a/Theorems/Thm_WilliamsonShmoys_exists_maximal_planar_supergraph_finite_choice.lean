-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_choice
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finite_choice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:39:18.709646+00:00
-- url     : https://prove2.me/theorems/8cb7009a-1ccd-41f1-b0a1-de001a512af2
-- title:
--   A drawable graph has a maximal drawable extension on a finite vertex set
-- statement:
--   Every drawable simple graph on a fixed finite vertex type is contained in a drawable graph with no strictly larger drawable supergraph on that vertex type. The proof route is to maximize edge count among the finite nonempty family of drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finite_choice
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
