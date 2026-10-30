-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T13:05:13.387473+00:00
-- url     : https://prove2.me/theorems/f27cd6ba-9373-4381-85e4-1e0b2c9cd75e
-- title:
--   Triangulated extension of a finite planar drawing
-- statement:
--   Every graph with a planar drawing on a finite vertex set of size at least three has a planar supergraph on that same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
