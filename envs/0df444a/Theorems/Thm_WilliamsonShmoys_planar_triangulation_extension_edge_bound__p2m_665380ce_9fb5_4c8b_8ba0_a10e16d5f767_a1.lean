-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:10:18.867529+00:00
-- url     : https://prove2.me/theorems/5b3bbe78-c4f5-4e6c-9476-97659c86e5a0
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a crossing-free supergraph on the same vertices whose edge count is exactly 3|V|−6. This is the triangulation-extension step; maximal planar extension and Euler’s formula give a proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_665380ce_9fb5_4c8b_8ba0_a10e16d5f767_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
