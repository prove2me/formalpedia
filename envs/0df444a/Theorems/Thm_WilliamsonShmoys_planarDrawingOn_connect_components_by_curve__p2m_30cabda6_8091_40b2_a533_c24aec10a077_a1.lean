-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- name    : WilliamsonShmoys.planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:16.322142+00:00
-- url     : https://prove2.me/theorems/635a1d24-9162-4bc8-8f51-e7db8e0ee893
-- title:
--   Join distinct components through the complement of a planar drawing
-- statement:
--   For a finite ordered vertex type, a drawing satisfying the given vertex, edge, and crossing conditions, and a disconnected graph with at least three vertices, there are ordered nonadjacent vertices and a continuous injective curve between their drawn points. The curve’s interior avoids every drawn vertex and every existing edge arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_connect_components_by_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1 {V : Type} [Fintype V] [LinearOrder V] (hV : 3 <= Fintype.card V) (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p) (hEdge : ∀ u v, u < v → G.Adj u v → ContinuousOn (arc u v) (Set.Icc 0 1) ∧ Set.InjOn (arc u v) (Set.Icc 0 1) ∧ arc u v 0 = p u ∧ arc u v 1 = p v ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y → (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) (hG_not_connected : ¬ G.Connected) : ∃ u v, u < v ∧ ¬ G.Adj u v ∧ ∃ γ : ℝ → ℝ × ℝ, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = p u ∧ γ 1 = p v ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y → ∀ s ∈ Set.Icc (0 : ℝ) 1, γ t ≠ arc x y s) := by sorry
