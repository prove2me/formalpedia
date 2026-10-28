-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_arc
-- name    : WilliamsonShmoys.planar_drawing_component_arc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:16:16.151817+00:00
-- url     : https://prove2.me/theorems/9a08e2fb-5b12-416d-8ed0-8e3fe4991bed
-- title:
--   Find an avoiding arc between distinct drawing components
-- statement:
--   From a finite crossing-free drawing and vertices in different connected components, obtain a drawing witness together with a simple continuous arc joining their locations. The arc interior avoids every drawn vertex and existing edge. The hypotheses retain both endpoint distinctness and failure of reachability; no additional positivity or size assumptions are needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_component_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v)
    (hnot : ¬ Relation.ReflTransGen G.Adj u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (γ : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → G.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)) ∧
      (∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.InjOn γ (Set.Icc 0 1) ∧
      γ 0 = p u ∧ γ 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          γ t ≠ arc x y s) := by
  sorry
