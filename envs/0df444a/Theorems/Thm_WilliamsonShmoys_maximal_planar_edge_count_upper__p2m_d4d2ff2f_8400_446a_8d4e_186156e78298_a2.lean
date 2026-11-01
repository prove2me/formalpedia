-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:52.517627+00:00
-- url     : https://prove2.me/theorems/e8818a47-c6bb-451e-9488-1f3faaa47e8f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This removes the general planar edge-bound argument from the parent. A proof route uses Euler’s formula and face-boundary counting, with the disconnected case handled as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
