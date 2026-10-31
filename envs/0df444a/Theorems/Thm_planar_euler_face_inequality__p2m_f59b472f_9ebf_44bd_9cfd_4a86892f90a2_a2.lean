-- Prove2me | Theorems.Thm_planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2
-- name    : planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:03.585747+00:00
-- url     : https://prove2.me/theorems/07c458c9-4133-43a0-8b95-3696befe2c71
-- title:
--   Euler relation and face-side bound for a connected planar graph
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a finite face count satisfying Euler’s relation, and each face contributes at least three edge sides in total.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard := by sorry
