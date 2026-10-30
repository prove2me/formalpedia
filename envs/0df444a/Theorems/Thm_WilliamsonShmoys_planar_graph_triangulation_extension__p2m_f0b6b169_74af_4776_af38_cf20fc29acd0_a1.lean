-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:18:02.760324+00:00
-- url     : https://prove2.me/theorems/ef71f331-24e3-40c9-8157-32dae1795a54
-- title:
--   Planar graphs extend to triangulations
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on that same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_triangulation_extension__p2m_f0b6b169_74af_4776_af38_cf20fc29acd0_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
