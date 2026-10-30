-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
-- name    : WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T04:55:43.983002+00:00
-- url     : https://prove2.me/theorems/58a549ee-4768-4664-9403-907071b96f48
-- title:
--   Finite face data from a planar drawing
-- statement:
--   For a connected graph with at least three vertices and a crossing-free drawing, there is a finite type of faces and a boundary length for each face. These satisfy Euler’s equation, each length is at least three, and the sum of the lengths is twice the edge count. These face and incidence facts are the exact topological input used by the parent; the parent sums the length bounds to obtain the requested inequality. A proof route is to derive the face walks from the cyclic order of arcs at each vertex, then establish Euler’s formula and count directed edge incidences. For a three-vertex tree, the sole face walk has length four, so the lower bound covers this boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.face_data_from_planar_drawing__p2m_2c2efb55_c875_4804_83b1_0ac0a059f6e4_a5 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ (F : Type) (inst : Fintype F) (length : F → Nat), @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧ (∀ f : F, 3 ≤ length f) ∧ (letI : Fintype F := inst; (∑ f : F, length f) = 2 * H.edgeSet.ncard) := by sorry
