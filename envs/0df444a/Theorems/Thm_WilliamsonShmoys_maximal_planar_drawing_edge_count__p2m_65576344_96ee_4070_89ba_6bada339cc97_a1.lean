-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:40:25.893185+00:00
-- url     : https://prove2.me/theorems/03e1b202-06dc-4da5-bd81-d67a28c40fa1
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   An edge-maximal planar graph on a finite vertex type with at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet.ncard ≤ H.edgeSet.ncard) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
