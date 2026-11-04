-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:33:14.880906+00:00
-- url     : https://prove2.me/theorems/c0d1c7a7-c3ce-45a1-a644-eb9b3fc28f42
-- title:
--   Planar edge upper bound
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges. This is the general planar extremal bound, proved from Euler’s formula; it does not require maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    letI : Fintype ↑K.edgeSet := Fintype.ofFinite _
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
