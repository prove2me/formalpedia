-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count_20261028
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:39:54.820204+00:00
-- url     : https://prove2.me/theorems/a4a29a79-57dd-442f-8226-0baca01e88d2
-- title:
--   Drawable graphs admit an exact maximal planar completion
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This also covers disconnected inputs: the completion can connect components before triangulating; when |V|=3, the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
