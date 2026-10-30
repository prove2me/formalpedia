-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- name    : WilliamsonShmoys.maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:32:59.071981+00:00
-- url     : https://prove2.me/theorems/00713f23-dc3f-40e2-9e32-872a4fb6b867
-- title:
--   Maximal drawable graphs satisfy the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraphs has at least `3|V| - 6` edges. This is the planar maximal-edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_edge_bound_fd0d87e6_b805_416b_90da_57eb1ca5807e
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
