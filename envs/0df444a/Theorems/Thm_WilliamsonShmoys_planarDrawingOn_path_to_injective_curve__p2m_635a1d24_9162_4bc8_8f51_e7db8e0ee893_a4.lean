-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
-- name    : WilliamsonShmoys.planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:14.511209+00:00
-- url     : https://prove2.me/theorems/bb286dfb-9295-4042-a06e-339ab0b1b6a8
-- title:
--   Simplify an avoiding path to an injective curve
-- statement:
--   Replace a continuous path with an injective continuous curve having the same endpoints and preserving its interior avoidance of vertices and edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p)
    {u v : V} (huv : u < v) (γ : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hzero : γ 0 = p u) (hone : γ 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hedges : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, γ t ≠ arc x y s) :
    ∃ γ' : ℝ → ℝ × ℝ,
      ContinuousOn γ' (Set.Icc 0 1) ∧ Set.InjOn γ' (Set.Icc 0 1) ∧
      γ' 0 = p u ∧ γ' 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ' t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, γ' t ≠ arc x y s) := by sorry
