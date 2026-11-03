-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:32.339685+00:00
-- url     : https://prove2.me/theorems/a9c9dbb0-74a5-4e80-aeeb-6c6cfc8d46c4
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing implies the usual planar edge bound e + 6 ≤ 3|V|. The drawing supplies a plane embedding; Euler’s formula and the lower bound of three on face boundary lengths give the inequality, including when the graph is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_3b0cc7ba_e438_41c2_b251_7b0cfc52f510_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
