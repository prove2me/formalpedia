-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:51.888002+00:00
-- url     : https://prove2.me/theorems/84aa0f8d-42a4-4615-a166-b73b4ced676a
-- title:
--   Connect a planar drawing with at least three vertices
-- statement:
--   A crossing-free drawing on a finite vertex type with at least three vertices can be extended, on the same vertex type, to a connected graph by adding edges while preserving a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
