-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:44.043847+00:00
-- url     : https://prove2.me/theorems/4d475df2-1a8a-43aa-9ce4-014b937605e8
-- title:
--   Planar graph triangulation extension with fixed vertex set
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_77d68189_39bf_4e13_b3a3_9f804ba94476_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G ≤ H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
