-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_plane_euler_data
-- name    : WilliamsonShmoys.edge_bound_of_plane_euler_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:01:29.298382+00:00
-- url     : https://prove2.me/theorems/716b72e0-4d9a-4e80-b2a1-b0f055ad00ed
-- title:
--   Edge bound from Euler face data
-- statement:
--   Euler’s vertex-face equation and the face-degree inequality imply the planar edge bound. If n is the vertex count, e the edge count, and f the face count, then n + f = e + 2 and 3f ≤ 2e; substitution gives e + 6 ≤ 3n. The hypothesis n ≥ 3 handles the natural-number subtraction in the conclusion. This child is proved by elementary natural-number arithmetic after unpacking the face data.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlaneEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_plane_euler_data
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hData : WilliamsonShmoys.HasPlaneEulerData G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
