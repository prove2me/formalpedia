-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:38.041266+00:00
-- url     : https://prove2.me/theorems/4dfbc005-ec61-47aa-85e1-1f450847f914
-- title:
--   Euler upper bound for a graph with a planar drawing
-- statement:
--   A simple graph on at least three vertices with the supplied crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
