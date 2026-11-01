-- Prove2me | Theorems.Thm_WilliamsonShmoys_spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1
-- name    : WilliamsonShmoys.spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:02:48.86946+00:00
-- url     : https://prove2.me/theorems/24fa2186-c188-443b-b73b-9b81dd69fcd0
-- title:
--   Spanning triangulation edge count for a connected planar drawing
-- statement:
--   Every finite connected simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices whose edge count is exactly 3|V|−6. The child packages the topological augmentation and Euler-counting argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    ∃ H : SimpleGraph U, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card U := by sorry
