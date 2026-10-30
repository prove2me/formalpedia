-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_0d153890
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_0d153890
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:18:38.870491+00:00
-- url     : https://prove2.me/theorems/1f8dbaa1-a35c-4928-ac7a-1a5c5c00316f
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertex type has exactly `3|V| − 6` edges. A proof shows maximality forces all faces to be triangles, then applies Euler’s formula; the lower bound on the number of vertices is retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_0d153890
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
