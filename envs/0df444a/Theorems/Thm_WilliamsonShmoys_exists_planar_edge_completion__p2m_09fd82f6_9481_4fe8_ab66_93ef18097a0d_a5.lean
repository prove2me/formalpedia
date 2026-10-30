-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- name    : WilliamsonShmoys.exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:15:26.859112+00:00
-- url     : https://prove2.me/theorems/90024f77-f5f3-4570-a30a-949bbf204bc3
-- title:
--   Completion of a finite plane graph to a triangulation
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing is contained in a crossing-free graph on the same vertex set whose edge count is exactly 3|V|−6. The drawing conditions are preserved while adding edges through complementary regions until the embedding is maximal and triangular.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
