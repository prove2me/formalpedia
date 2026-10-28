-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:26:10.396544+00:00
-- url     : https://prove2.me/theorems/917c2594-b87d-4860-92b1-bb3b9637d0ca
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   On a finite vertex type, every drawable graph lies inside a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_fd0d87e6_b805_416b_90da_57eb1ca5807e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
