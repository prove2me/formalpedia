-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:21:44.937473+00:00
-- url     : https://prove2.me/theorems/03ed2ab0-efc9-4bea-b7ff-50f9e41807dc
-- title:
--   Euler and triangular-face counts for a maximal drawable graph
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a natural face count satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_c73cf9ba_fcca_4a3b_853a_2c4df1119a23_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
