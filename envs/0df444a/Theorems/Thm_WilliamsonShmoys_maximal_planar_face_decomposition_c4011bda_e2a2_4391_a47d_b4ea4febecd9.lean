-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:49:26.445247+00:00
-- url     : https://prove2.me/theorems/b9c5050b-a13a-4e78-9abb-6610ad4bb1a1
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has a face count satisfying Euler’s equation and the triangular-face incidence equation. Together these equations yield the target edge count. The three-vertex boundary case is included: its maximal drawable graph is a triangle, with two faces counted on the sphere.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
