-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:50:48.574905+00:00
-- url     : https://prove2.me/theorems/646b0e38-73f2-4ec6-a3f4-a1fa63914061
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
