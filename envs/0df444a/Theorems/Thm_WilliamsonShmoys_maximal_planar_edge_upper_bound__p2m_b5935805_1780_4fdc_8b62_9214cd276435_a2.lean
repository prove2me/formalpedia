-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:37.815305+00:00
-- url     : https://prove2.me/theorems/8eefeb5d-6bb8-407d-b469-57becc19650a
-- title:
--   Euler edge bound for a finite planar simple graph
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3|V| − 6 edges. This supplies the upper bound in the parent equality. A proof route uses Euler’s formula and counts face degrees, accounting for disconnected components before weakening to this bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
