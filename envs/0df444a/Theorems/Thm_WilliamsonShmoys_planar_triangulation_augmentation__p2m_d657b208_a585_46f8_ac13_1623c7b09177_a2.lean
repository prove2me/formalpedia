-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- name    : WilliamsonShmoys.planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:13:13.751801+00:00
-- url     : https://prove2.me/theorems/e8d830f7-8876-4fbd-9d43-eb90e96cd3c0
-- title:
--   Planar augmentation reaches the triangulation edge threshold
-- statement:
--   For any drawable simple graph on at least three vertices, one can add edges on the same vertex set while preserving planarity until the edge count is at least 3|V|−6. The local instance is scoped as a term-level let, avoiding the prior failed tactic block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_augmentation__p2m_d657b208_a585_46f8_ac13_1623c7b09177_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G <= H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel _;
       3 * Fintype.card V - 6 <= H.edgeFinset.card) := by sorry
