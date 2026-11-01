-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:24.538217+00:00
-- url     : https://prove2.me/theorems/6683070b-8f0f-4f85-989e-81cd2560323f
-- title:
--   Triangulate a finite planar drawing without adding vertices
-- statement:
--   Any finite drawable simple graph with at least three vertices has a drawable simple supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
