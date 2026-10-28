-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_sup_from_clean_arc
-- name    : WilliamsonShmoys.planar_drawingOn_sup_from_clean_arc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:23:16.202477+00:00
-- url     : https://prove2.me/theorems/17b13b92-fbc0-495e-b1fb-0c50a61f1a81
-- title:
--   Draw the graph after adding a clean arc
-- statement:
--   For the graph formed by adjoining the unordered edge between `u` and `v` to `G`, construct a planar drawing from the given drawing of `G` and the clean arc `γ`. The endpoint, continuity, injectivity, vertex avoidance, and crossing hypotheses supply exactly the required drawing properties. This statement does not require `u` and `v` to be unreachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawingOn_sup_from_clean_arc
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
    WilliamsonShmoys.HasPlanarDrawingOn
      (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)) := by sorry
