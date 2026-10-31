-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_arc_for_unreachable_vertices__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
-- name    : WilliamsonShmoys.planar_drawing_arc_for_unreachable_vertices__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:54.617739+00:00
-- url     : https://prove2.me/theorems/0af253c7-2e49-42a9-bbb4-7bacf71124fd
-- title:
--   Join a specified pair of unreachable vertices through the drawing’s complement
-- statement:
--   Given a crossing-free drawing and an ordered pair of unreachable vertices, the pair is nonadjacent and can be joined by a simple continuous arc whose interior misses every drawn vertex and edge arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_arc_for_unreachable_vertices__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ u v, u < v → K.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (huv : u < v) (hnr : ¬ K.Reachable u v) :
    ¬ K.Adj u v ∧
      ∃ gamma : ℝ → ℝ × ℝ,
        ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
        gamma 0 = p u ∧ gamma 1 = p v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
          ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) := by
  sorry
