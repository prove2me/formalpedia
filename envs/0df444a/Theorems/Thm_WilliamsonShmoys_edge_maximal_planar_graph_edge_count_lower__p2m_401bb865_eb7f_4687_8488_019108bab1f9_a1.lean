-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:15.761374+00:00
-- url     : https://prove2.me/theorems/2d4d5aa9-1174-4f98-adfa-d1e94ce87256
-- title:
--   Maximality lower bound for planar graph edges
-- statement:
--   A maximal finite simple planar graph on at least three vertices has at least 3|V|−6 edges; maximality forces a triangulation, and Euler counting gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ->
      (forall u v, N.Adj u v -> P.Adj u v) -> P = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
