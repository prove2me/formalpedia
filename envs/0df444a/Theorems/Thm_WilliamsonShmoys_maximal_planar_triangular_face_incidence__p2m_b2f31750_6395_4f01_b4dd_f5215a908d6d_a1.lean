-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- name    : WilliamsonShmoys.maximal_planar_triangular_face_incidence__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:31.607603+00:00
-- url     : https://prove2.me/theorems/0573be99-03f8-47a3-beea-1ebc73ce1534
-- title:
--   Triangular face incidence in a maximal planar graph
-- statement:
--   For a connected maximal planar graph with at least three vertices, some natural face count satisfies the triangular face-incidence equation. A proof route is to extract a plane embedding, show each face is triangular because a missing diagonal could otherwise be drawn inside it, and count each edge twice across face boundaries. This isolates the use of maximality and preserves the lower bound needed to handle small face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangular_face_incidence__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ f : ℕ, 3 * f = 2 * N.edgeFinset.card := by sorry
