-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:44:42.751113+00:00
-- url     : https://prove2.me/theorems/2caa5445-5382-49b4-aef1-d1703ac143a6
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing is a subgraph of a graph on the same vertices that also has a crossing-free drawing and exactly 3n − 6 edges. The proof route is to add noncrossing edges until the embedding is maximal, establish that the resulting faces are triangles, and combine Euler’s formula with the face-edge count. This child isolates the topological augmentation and Euler work from the parent’s edge-set monotonicity and arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_92968d93_3ce8_4b3b_823b_5613f2821c0d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
