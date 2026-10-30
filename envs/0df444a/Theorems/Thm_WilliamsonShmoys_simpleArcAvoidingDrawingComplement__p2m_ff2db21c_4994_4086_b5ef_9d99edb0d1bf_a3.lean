-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3
-- name    : WilliamsonShmoys.simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:24.887815+00:00
-- url     : https://prove2.me/theorems/92e9ec78-8091-49a8-9a43-2350363b96d8
-- title:
--   Simplify a path in the drawing complement
-- statement:
--   For a continuous path whose interior avoids every vertex location and every drawn edge, there is an injective continuous path with the same endpoints whose interior has the same avoidance properties.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = p u ∧ delta 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, delta t ≠ arc x y s) := by sorry
