-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- name    : WilliamsonShmoys.planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:45.700431+00:00
-- url     : https://prove2.me/theorems/ce11034e-9d40-4f95-bd08-a8f0a5d53ed0
-- title:
--   Face counts from a crossing-free drawing
-- statement:
--   For a connected simple graph with at least three vertices and the supplied crossing-free drawing, obtain a face count satisfying Euler’s equation and the boundary-side count. Bridges contribute both sides to boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count_data__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = M.edgeFinset.card + 2 ∧ 3 * f ≤ 2 * M.edgeFinset.card := by sorry
