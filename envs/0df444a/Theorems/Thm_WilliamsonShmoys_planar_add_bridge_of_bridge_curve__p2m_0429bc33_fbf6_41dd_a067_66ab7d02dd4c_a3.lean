-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
-- name    : WilliamsonShmoys.planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:22.782091+00:00
-- url     : https://prove2.me/theorems/02853d91-2027-4c7f-9261-be16db6326ab
-- title:
--   Insert an edge along an admissible bridge curve
-- statement:
--   Extend the graph by exactly the selected pair and extend the drawing using the supplied bridge curve. The explicit conditions on the old drawing and bridge curve ensure continuity, injectivity, vertex avoidance, and allowed intersections for the extended drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_bridge_of_bridge_curve__p2m_0429bc33_fbf6_41dd_a067_66ab7d02dd4c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (x y : V)
    (hxy : ¬ G.Reachable x y)
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
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
      HasPlanarDrawingOn N := by sorry
