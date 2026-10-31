-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
-- name    : WilliamsonShmoys.planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:57:23.360988+00:00
-- url     : https://prove2.me/theorems/6cc89dc0-dca8-4f92-990f-6ab07c5977c9
-- title:
--   Planar drawing augmentation to a triangulated edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
