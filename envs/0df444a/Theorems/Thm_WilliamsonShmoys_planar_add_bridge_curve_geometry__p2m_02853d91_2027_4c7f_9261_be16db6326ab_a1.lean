-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_curve_geometry__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a1
-- name    : WilliamsonShmoys.planar_add_bridge_curve_geometry__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:03:16.748328+00:00
-- url     : https://prove2.me/theorems/9fe4e022-58de-4ff0-aac0-7e9caf0fd959
-- title:
--   Extend a planar drawing across a bridge curve
-- statement:
--   For a graph whose edges are exactly the old edges together with the selected pair, extend the given crossing-free drawing using the admissible bridge curve.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_bridge_curve_geometry__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G N : SimpleGraph V)
    (x y : V)
    (hxy : ¬ G.Reachable x y)
    (hAdj : ∀ u v, N.Adj u v ↔
      G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)))
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hDrawing :
      Function.Injective p ∧
        (∀ u v, u < v → G.Adj u v →
          ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
        (∀ u v a b, u < v → a < b → G.Adj u v → G.Adj a b →
          (u, v) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc u v t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hBridge :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
        γ 0 = p x ∧ γ 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
        (∀ u v, u < v → G.Adj u v →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            γ t = arc u v s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    HasPlanarDrawingOn N := by sorry
