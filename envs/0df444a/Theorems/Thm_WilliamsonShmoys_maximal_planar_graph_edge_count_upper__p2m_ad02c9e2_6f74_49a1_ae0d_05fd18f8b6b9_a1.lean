-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:37.854705+00:00
-- url     : https://prove2.me/theorems/c613d228-2a90-40f8-8150-998155f5275e
-- title:
--   Euler edge bound for maximal planar graphs
-- statement:
--   A graph on at least three vertices that has a crossing-free drawing and is maximal among planar supergraphs on that same vertex set has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_ad02c9e2_6f74_49a1_ae0d_05fd18f8b6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
