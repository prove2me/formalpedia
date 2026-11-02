-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:49:26.507125+00:00
-- url     : https://prove2.me/theorems/9aae8c1a-0088-4039-a6d9-b99fa0bd700a
-- title:
--   Planar drawings extend to a triangulation on the same vertices
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices that has a crossing-free drawing is a subgraph of a graph on the same vertices that has a crossing-free drawing and exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_f2e67bcd_d844_4f8f_86df_68d56c93483a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
