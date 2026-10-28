-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_dense_extension
-- name    : WilliamsonShmoys.planar_drawable_dense_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:55:57.683701+00:00
-- url     : https://prove2.me/theorems/a72cf706-e493-49e9-966a-058a42f60774
-- title:
--   A drawable graph has a dense drawable supergraph
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices is a subgraph of another drawable graph on the same vertices whose edge count is at least 3|V|−6. This is the triangulation and Euler-formula step; the parent uses maximality to show the supergraph has exactly H’s edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_dense_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
