-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:11.452553+00:00
-- url     : https://prove2.me/theorems/30cffe24-7203-4ddb-9bd1-f31532d2c872
-- title:
--   Simple planar graph edge bound for connected graphs
-- statement:
--   A connected finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler and face-counting core; the order, drawing, and cardinality hypotheses are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
