-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_unreachable_pair_avoiding_arc__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
-- name    : WilliamsonShmoys.planarDrawing_unreachable_pair_avoiding_arc__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:52.953613+00:00
-- url     : https://prove2.me/theorems/249812fe-a756-4e03-b836-d8cf2553a6f0
-- title:
--   A planar drawing admits an avoiding arc between unreachable vertices
-- statement:
--   For a specified ordered, nonadjacent pair in distinct reachability classes, the crossing-free drawing admits a continuous injective joining arc with the required endpoint values and with interior disjoint from all vertices and drawn edges. This isolates the topological construction used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_unreachable_pair_avoiding_arc__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p ∧ (∀ u v, u < v → H.Adj u v → ContinuousOn (arc u v) (Set.Icc 0 1) ∧ Set.InjOn (arc u v) (Set.Icc 0 1) ∧ arc u v 0 = p u ∧ arc u v 1 = p v ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧ (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y → (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) (u v : V) (huv : u < v) (hnotAdj : ¬ H.Adj u v) (hnotReachable : ¬ H.Reachable u v) : ∃ gamma : ℝ → ℝ × ℝ, ContinuousOn gamma (Set.Icc 0 1) ∧ Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y → ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) := by sorry
