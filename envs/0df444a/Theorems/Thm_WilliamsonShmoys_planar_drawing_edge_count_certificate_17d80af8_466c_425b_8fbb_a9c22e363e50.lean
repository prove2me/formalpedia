-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50
-- name    : WilliamsonShmoys.planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:54:53.365594+00:00
-- url     : https://prove2.me/theorems/7c1cdf82-a9e5-438a-b5c9-f342f3f36883
-- title:
--   Euler and face-incidence certificate for a connected planar drawing
-- statement:
--   For a finite connected simple graph on at least three vertices with the specified crossing-free drawing, there is a natural face count satisfying Euler’s relation and the face-boundary incidence inequality. This removes the geometric and topological work from the parent, leaving only arithmetic. A proof route is to extract a rotation system from the finite plane embedding, apply Euler’s formula for a connected embedding, and count edge sides in face boundary walks; every face walk has length at least three, including when bridges are present.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard := by sorry
