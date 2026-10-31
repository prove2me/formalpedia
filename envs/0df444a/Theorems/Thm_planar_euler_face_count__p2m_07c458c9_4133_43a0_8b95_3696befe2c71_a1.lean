-- Prove2me | Theorems.Thm_planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- name    : planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:26.812617+00:00
-- url     : https://prove2.me/theorems/60f5bd7b-5404-406f-a7fd-ea63b03fcd8c
-- title:
--   Euler face count for a connected planar graph
-- statement:
--   For a finite connected graph with at least three vertices and a crossing-free drawing, there is a natural face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem planar_euler_face_count__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
