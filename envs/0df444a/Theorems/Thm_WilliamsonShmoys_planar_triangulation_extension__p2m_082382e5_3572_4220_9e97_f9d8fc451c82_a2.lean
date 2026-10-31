-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:46.436075+00:00
-- url     : https://prove2.me/theorems/e311c4a7-aff6-4403-a1d3-f4a962b82e69
-- title:
--   Extend a drawn planar graph to a triangulation on the same vertices
-- statement:
--   Given a finite simple graph with a crossing-free drawing and at least three vertices, extend it on the same vertices to a drawn planar graph with exactly 3|V|−6 edges, retaining every original edge. The proof adds noncrossing edges within faces until the extension is edge-maximal, joins distinct components through the complement when necessary, and applies Euler’s formula after showing maximality forces triangular faces. The lower bound of three vertices ensures the usual triangulation edge count applies; disconnected inputs are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_082382e5_3572_4220_9e97_f9d8fc451c82_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
