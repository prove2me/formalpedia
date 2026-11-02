-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:35:33.394375+00:00
-- url     : https://prove2.me/theorems/bab66b79-6592-402f-91eb-32b2082996b1
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices extends, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
