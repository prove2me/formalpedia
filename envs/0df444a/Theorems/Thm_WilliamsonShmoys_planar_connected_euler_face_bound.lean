-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_euler_face_bound
-- name    : WilliamsonShmoys.planar_connected_euler_face_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:14:24.924928+00:00
-- url     : https://prove2.me/theorems/b06d3ee5-790d-46a7-ad1f-7d1c9d220177
-- title:
--   Euler face-count bound for a connected simple plane graph
-- statement:
--   For a connected finite simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces f such that Euler’s formula holds and the sum of face-boundary lengths is at least three per face. The latter follows by counting the two sides of every edge and using that no face boundary has length one or two in this setting; bridges are counted with both sides, even when the same edge occurs twice on a boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_euler_face_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
