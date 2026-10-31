-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:26.076862+00:00
-- url     : https://prove2.me/theorems/1fc721c4-d4d8-4a3d-8e5b-8d3e1462bbc6
-- title:
--   Adding an edge below the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3n−6 edges, then a strictly larger drawable graph can be formed on the same vertex set by adding an edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_bf9be5f4_efbc_4928_a7c5_3fcb68a1a21a_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hSmall : S.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ T : SimpleGraph V, S ≤ T ∧ T ≠ S ∧ WilliamsonShmoys.HasPlanarDrawingOn T := by sorry
