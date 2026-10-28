-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:26:16.540796+00:00
-- url     : https://prove2.me/theorems/3fe8be02-4541-4d0a-bbf4-850e46d722fe
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by sorry
