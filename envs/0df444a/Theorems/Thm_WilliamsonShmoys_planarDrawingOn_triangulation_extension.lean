-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulation_extension
-- name    : WilliamsonShmoys.planarDrawingOn_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:11:47.360406+00:00
-- url     : https://prove2.me/theorems/cd0a3fa1-4d8b-47c1-8dcf-23068fbd35cd
-- title:
--   Extend a planar drawing to a triangulated planar supergraph
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices is contained, on the same vertex set, in a planar triangulation with exactly 3n−6 edges. The boundary case n=3 is included. Prove this by adding noncrossing edges through faces until no more can be added, then apply Euler’s formula and count face-edge incidences. The formalization must establish that each augmentation preserves the supplied arc-based drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
