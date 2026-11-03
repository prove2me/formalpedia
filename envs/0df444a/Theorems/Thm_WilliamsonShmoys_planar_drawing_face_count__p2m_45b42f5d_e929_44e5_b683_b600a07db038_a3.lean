-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:22.797715+00:00
-- url     : https://prove2.me/theorems/817efdd6-f4a1-4a63-bdc1-5f87cd74d1d4
-- title:
--   Finite face count from a crossing-free graph drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite face count satisfying Euler’s equation and the standard lower bound on total face degree.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 ∧ 3 * f ≤ 2 * M.edgeFinset.card := by sorry
