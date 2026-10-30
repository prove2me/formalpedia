-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:10:54.983176+00:00
-- url     : https://prove2.me/theorems/0b4dfd6f-06c1-4308-ac8f-c613b2449d02
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A maximal drawable graph on at least three vertices has a natural-number face count satisfying Euler’s equation and the triangular-face incidence equation. Together these yield the exact maximal planar edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count_6274f47d_124c_4fd1_84e6_71540a951a1f
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
