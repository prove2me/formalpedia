-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:34.923705+00:00
-- url     : https://prove2.me/theorems/fe481bb3-5bd3-4632-91f8-3ed33818ce05
-- title:
--   Connected planar supergraph existence
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by sorry
