-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- name    : WilliamsonShmoys.maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:00.049812+00:00
-- url     : https://prove2.me/theorems/324069a7-d0a2-45e0-94ba-3f9b77cc47fd
-- title:
--   Euler and triangular-face counts for a maximal planar drawing
-- statement:
--   For a connected inclusion-maximal graph with the given crossing-free drawing and at least three vertices, there is a finite number of faces F such that Euler’s formula holds and the total triangular face-side count is twice the edge count. Prove by converting the drawing to a plane embedding, applying Euler’s formula, and using maximality to show every face has degree three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_embedding_counts__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ F : ℕ,
      (Fintype.card V : ℤ) - (L.edgeFinset.card : ℤ) + (F : ℤ) = 2 ∧
      3 * F = 2 * L.edgeFinset.card := by sorry
