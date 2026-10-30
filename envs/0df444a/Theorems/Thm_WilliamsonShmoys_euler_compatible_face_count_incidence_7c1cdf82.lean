-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_compatible_face_count_incidence_7c1cdf82
-- name    : WilliamsonShmoys.euler_compatible_face_count_incidence_7c1cdf82
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:09:12.161796+00:00
-- url     : https://prove2.me/theorems/4d0c2802-8f3b-4d79-b31d-d0704c9c8543
-- title:
--   Incidence bound for an Euler-compatible face count
-- statement:
--   For a finite connected simple graph with the specified crossing-free drawing and at least three vertices, every natural number satisfying Euler’s equation obeys the face-incidence inequality. A proof can establish the simple planar edge bound by counting face-boundary edge sides, then use the supplied Euler equation and arithmetic. The vertex lower bound is retained to rule out the small-graph exception.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.euler_compatible_face_count_incidence_7c1cdf82 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) (f : Nat) (heuler : Fintype.card V + f = H.edgeSet.ncard + 2) : 3 * f ≤ 2 * H.edgeSet.ncard := by sorry
