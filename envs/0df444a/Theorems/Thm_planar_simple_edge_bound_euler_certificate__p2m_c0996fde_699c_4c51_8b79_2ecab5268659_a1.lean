-- Prove2me | Theorems.Thm_planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1
-- name    : planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:29.490993+00:00
-- url     : https://prove2.me/theorems/7c79708d-854c-4714-8264-d2d977d1ffbf
-- title:
--   Euler face certificate for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a face count satisfying Euler’s formula and the total face-degree lower bound. This isolates the topological face-counting work; the parent combines the two inequalities arithmetically to obtain the edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem planar_simple_edge_bound_euler_certificate__p2m_c0996fde_699c_4c51_8b79_2ecab5268659_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  sorry
