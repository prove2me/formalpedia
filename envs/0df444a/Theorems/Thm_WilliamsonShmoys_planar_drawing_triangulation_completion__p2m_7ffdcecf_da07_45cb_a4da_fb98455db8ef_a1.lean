-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:52.375205+00:00
-- url     : https://prove2.me/theorems/05876c00-4f7e-4d9e-b91e-0da976d19dc6
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex type, to a drawable supergraph having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_7ffdcecf_da07_45cb_a4da_fb98455db8ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
