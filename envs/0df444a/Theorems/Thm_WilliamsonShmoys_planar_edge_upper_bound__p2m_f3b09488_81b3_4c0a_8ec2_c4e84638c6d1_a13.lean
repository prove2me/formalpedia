-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a13
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a13
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:07:46.817161+00:00
-- url     : https://prove2.me/theorems/5280a2aa-60f7-4202-882a-cd0ab3286ee5
-- title:
--   Planar simple graphs have at most 3n−6 edges
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most `3|V|−6` edges. This supplies the upper half of the parent equality. A proof route is to use the drawing to establish the planar Euler edge inequality and bound face-edge incidences, accounting for disconnected graphs and preserving the `|V| = 3` case. The formal source definition requires disjoint edge interiors and excludes other vertices from edge interiors.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a13
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
