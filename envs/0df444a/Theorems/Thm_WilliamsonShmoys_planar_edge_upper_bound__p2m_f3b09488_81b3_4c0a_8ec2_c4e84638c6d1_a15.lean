-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:30.190719+00:00
-- url     : https://prove2.me/theorems/37f18342-0daf-4a16-a04d-b1248ece3f6a
-- title:
--   Planar simple graphs have at most 3n−6 edges
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the upper half of the parent equality. The drawing definition supplies injective vertex positions, non-self-intersecting edge arcs, and disjoint edge interiors; the proof must derive an Euler-style bound from these conditions, including for disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a15
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
