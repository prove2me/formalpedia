-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:30.375195+00:00
-- url     : https://prove2.me/theorems/6162c346-56e0-4291-a049-fac9204b7241
-- title:
--   Euler and face-incidence counts for maximal planar drawings
-- statement:
--   For a drawable graph on at least three finite ordered vertices that is maximal among drawable supergraphs on the same vertex type, there is a natural number f satisfying the triangular face-incidence count and Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_euler_face_counts__p2m_77e6a9aa_019b_4811_bd18_07d7e3258778_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    ∃ f : ℕ,
      2 * K.edgeSet.ncard = 3 * f ∧
      Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
