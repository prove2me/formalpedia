-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:17.149902+00:00
-- url     : https://prove2.me/theorems/2b72ef1b-a6e4-48f4-be00-773195a8c334
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every graph with a planar drawing has a planar supergraph on the same finite vertex type that contains its edges, has at least as many edges, and has maximum edge count among its planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) : ∃ H : SimpleGraph V, (∀ u v, Y.Adj u v → H.Adj u v) ∧ Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
