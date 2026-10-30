-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count
-- name    : WilliamsonShmoys.planar_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:03:53.945218+00:00
-- url     : https://prove2.me/theorems/38ee3d54-10ff-40a6-926a-e5dee778186d
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable graphs on the same vertex set has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
