-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:02.621829+00:00
-- url     : https://prove2.me/theorems/02e9e0aa-44ab-46d6-9b9b-757e7ba4e790
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   Any finite graph with a crossing-free drawing can be extended, on the same vertex set, to a connected graph with a crossing-free drawing, while preserving all original edges. Its edge count therefore does not decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       H.edgeFinset.card ≤ K.edgeFinset.card) ∧
      K.Connected := by sorry
