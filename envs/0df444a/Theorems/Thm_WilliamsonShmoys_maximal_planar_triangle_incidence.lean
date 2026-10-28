-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangle_incidence
-- name    : WilliamsonShmoys.maximal_planar_triangle_incidence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:25:40.505952+00:00
-- url     : https://prove2.me/theorems/d1156ce4-1ba6-423a-8979-96c05074c84b
-- title:
--   Triangular face-edge incidence for a maximal planar drawing
-- statement:
--   When f is the Euler face count of a maximal drawable simple graph with at least three vertices, every face is triangular, so counting edge incidences over faces gives 3f = 2|E|. A proof can first establish that maximality forces 2-connectedness and then use the possibility of adding a noncrossing diagonal to rule out faces with boundary length greater than three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_triangle_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ) :
    Fintype.card V + f = H.edgeSet.ncard + 2 →
    3 * f = 2 * H.edgeSet.ncard := by sorry
