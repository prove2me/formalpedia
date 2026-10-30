-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:01:25.940696+00:00
-- url     : https://prove2.me/theorems/ec135dca-b35f-4690-a88a-60012f6a0abd
-- title:
--   A maximal drawable graph has the planar extremal edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertex type has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
