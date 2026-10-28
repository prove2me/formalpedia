-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_clean_arc_of_unreachable
-- name    : WilliamsonShmoys.planar_drawing_clean_arc_of_unreachable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:51:38.448106+00:00
-- url     : https://prove2.me/theorems/dd81f56d-4d2a-49be-a775-3333fca653b1
-- title:
--   Join unreachable vertices by a clean arc
-- statement:
--   For the specified drawing of a graph, construct an injective continuous arc between ordered unreachable vertices. Its interior avoids every vertex, and any intersection with an existing edge arc occurs only at endpoints. This is the main topological obligation; a proof route uses the faces of the finite embedded graph or regular neighborhoods of its components to route through the complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_clean_arc_of_unreachable
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u < v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (γ : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.InjOn γ (Set.Icc 0 1) ∧
      γ 0 = p u ∧ γ 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
