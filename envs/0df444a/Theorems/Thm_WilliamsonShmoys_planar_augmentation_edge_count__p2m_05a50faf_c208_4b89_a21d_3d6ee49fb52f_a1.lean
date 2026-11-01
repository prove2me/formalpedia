-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1
-- name    : WilliamsonShmoys.planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:07.962131+00:00
-- url     : https://prove2.me/theorems/7b09e600-7df3-4cde-9f3e-028247bb9b4a
-- title:
--   Planar augmentation to the triangulated edge count
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing predicate and at least three vertices has a planar supergraph on the same vertex set with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_edge_count__p2m_05a50faf_c208_4b89_a21d_3d6ee49fb52f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
