-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:18.712561+00:00
-- url     : https://prove2.me/theorems/e5df8253-ddef-477a-b1f4-10bf2b09b315
-- title:
--   Extend a finite planar graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
