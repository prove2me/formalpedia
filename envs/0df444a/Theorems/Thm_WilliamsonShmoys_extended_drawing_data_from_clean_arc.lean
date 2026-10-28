-- Prove2me | Theorems.Thm_WilliamsonShmoys_extended_drawing_data_from_clean_arc
-- name    : WilliamsonShmoys.extended_drawing_data_from_clean_arc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:51:50.198011+00:00
-- url     : https://prove2.me/theorems/f5267f8e-492b-412f-82dc-4f2391d59235
-- title:
--   Extend drawing data by a clean arc
-- statement:
--   Keeping the vertex map fixed, construct an arc assignment witnessing all the drawing conditions for the graph obtained by adding the edge `(u,v)`. The arc assignment should preserve every old edge arc and use the supplied clean arc for the added edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.extended_drawing_data_from_clean_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arc x y) (Set.Icc 0 1) ∧
      Set.InjOn (arc x y) (Set.Icc 0 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hCross : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
      (x, y) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc x y t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hγContinuous : ContinuousOn γ (Set.Icc 0 1))
    (hγInjective : Set.InjOn γ (Set.Icc 0 1))
    (hγStart : γ 0 = p u)
    (hγEnd : γ 1 = p v)
    (hγAvoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγCross : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ arcNew : V → V → ℝ → ℝ × ℝ,
      (∀ x y, x < y →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj x y →
        ContinuousOn (arcNew x y) (Set.Icc 0 1) ∧
        Set.InjOn (arcNew x y) (Set.Icc 0 1) ∧
        arcNew x y 0 = p x ∧ arcNew x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arcNew x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj x y →
        (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)).Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arcNew x y t = arcNew a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
