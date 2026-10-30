-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:09.247427+00:00
-- url     : https://prove2.me/theorems/6d61c34e-acf2-4651-8c9f-45d89df1db8f
-- title:
--   Planar triangulation extension on a fixed vertex set
-- statement:
--   Any finite planar graph on at least three vertices has a planar supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_c8bd0d06_bddd_4d97_9a5a_50d50f58bad7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
