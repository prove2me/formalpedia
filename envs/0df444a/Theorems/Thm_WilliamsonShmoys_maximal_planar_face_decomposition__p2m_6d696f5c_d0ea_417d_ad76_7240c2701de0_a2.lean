-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:52:10.448172+00:00
-- url     : https://prove2.me/theorems/8e1600a0-c8bc-4843-bba9-210511d5f55d
-- title:
--   Euler and triangular-face equations for a maximal drawable graph
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a natural-number face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_6d696f5c_d0ea_417d_ad76_7240c2701de0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
