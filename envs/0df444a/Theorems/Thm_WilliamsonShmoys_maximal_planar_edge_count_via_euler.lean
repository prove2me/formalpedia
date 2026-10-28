-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler
-- name    : WilliamsonShmoys.maximal_planar_edge_count_via_euler
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:41:02.980983+00:00
-- url     : https://prove2.me/theorems/878ec71d-08cc-4a41-abbd-c7169c10da84
-- title:
--   A maximal drawable graph has the planar triangulation edge count
-- statement:
--   A drawable graph on at least three vertices with no strict drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_via_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hSmax : ∀ T : SimpleGraph V,
      S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
