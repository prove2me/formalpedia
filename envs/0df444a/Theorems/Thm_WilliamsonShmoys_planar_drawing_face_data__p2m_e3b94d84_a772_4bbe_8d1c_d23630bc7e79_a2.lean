-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:03.822929+00:00
-- url     : https://prove2.me/theorems/6958ede2-46bd-4413-bb7d-9bd4b5c0d4f2
-- title:
--   Extract Euler face data from a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a finite face count satisfying Euler’s equation and a lower bound of three on total face-boundary incidences. This isolates the drawing-to-combinatorial-embedding and face-counting work. A proof route is to extract a rotation system from the arcs, form its face-boundary walks, apply Euler’s formula for the resulting plane embedding, and count the two side incidences of each edge. Simplicity and the vertex lower bound rule out face walks of length one or two; connectedness handles bridge traversals within the walks. This topological conversion remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_e3b94d84_a772_4bbe_8d1c_d23630bc7e79_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard := by sorry
