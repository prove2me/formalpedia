-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_triangle_face_count
-- name    : WilliamsonShmoys.maximal_planar_euler_triangle_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:44:45.460338+00:00
-- url     : https://prove2.me/theorems/d51190b1-8a07-4935-b1e8-3fdecb95c1b0
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a maximal drawable graph on at least three vertices, a natural face count satisfies Euler’s vertex-face-edge equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_triangle_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
