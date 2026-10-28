-- Prove2me | Theorems.Thm_WilliamsonShmoys_safe_bridge_between_unreachable_vertices
-- name    : WilliamsonShmoys.safe_bridge_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:46:45.154343+00:00
-- url     : https://prove2.me/theorems/127851b9-b2d3-4002-82f8-72b653ff1c80
-- title:
--   An unreachable pair in a finite plane drawing admits a safe arc
-- statement:
--   Given a finite crossing-free drawing and two distinct unreachable vertices, construct a continuous injective arc between their positions whose interior avoids every vertex and whose intersections with old edges occur only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.safe_bridge_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdgeDrawing : ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arc x y) (Set.Icc 0 1) ∧
      Set.InjOn (arc x y) (Set.Icc 0 1) ∧
      arc x y 0 = p x ∧
      arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hNoCrossing : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
      (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (huv : u < v) (hUnreachable : ¬ G.Reachable u v) :
    ∃ bridge : ℝ → ℝ × ℝ,
      ContinuousOn bridge (Set.Icc 0 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          bridge t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
