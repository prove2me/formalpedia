-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:11.130205+00:00
-- url     : https://prove2.me/theorems/4f728ae5-300b-4f49-98db-5976840980d8
-- title:
--   Planar triangulation completion on a fixed vertex set
-- statement:
--   Every finite simple graph with at least three vertices that has the supplied planar drawing can be extended, without adding vertices, to a planar graph with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
