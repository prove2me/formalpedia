-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:13.806682+00:00
-- url     : https://prove2.me/theorems/61248ae6-40fa-4602-aefc-9bbed6da1387
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with the specified crossing-free drawing and at least three vertices has at most 3n − 6 edges. The vertex lower bound is necessary for this formulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
