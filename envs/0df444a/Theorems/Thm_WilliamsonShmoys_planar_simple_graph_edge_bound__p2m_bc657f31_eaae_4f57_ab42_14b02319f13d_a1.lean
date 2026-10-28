-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:37:57.439501+00:00
-- url     : https://prove2.me/theorems/96ae6d88-fda1-42e5-9f5b-cc899dd909d2
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has at most 3|V|−6 edges. At |V|=3 this permits exactly three edges, as in the triangle; the statement is an upper bound and allows fewer edges for nonmaximal graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
