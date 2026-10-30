-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleArcInteriorAvoidingFinitePoints__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a1
-- name    : WilliamsonShmoys.simpleArcInteriorAvoidingFinitePoints__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:25:16.795023+00:00
-- url     : https://prove2.me/theorems/d153ce94-262b-4826-8f60-ae8ab62a4995
-- title:
--   Join distinct points by an arc avoiding finitely many points
-- statement:
--   For a finite family of points in the plane and two distinct members, there is a continuous injective arc between those two points whose interior avoids every point in the family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleArcInteriorAvoidingFinitePoints__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a1
    {V : Type} [Fintype V]
    (p : V → ℝ × ℝ) (u v : V) (hpuv : p u ≠ p v) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = p u ∧
      delta 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) := by sorry
