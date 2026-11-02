-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- name    : WilliamsonShmoys.planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:05.396046+00:00
-- url     : https://prove2.me/theorems/3e6d8a60-d3d3-4ec8-8c95-56c4b76ce917
-- title:
--   Redraw disconnected components to leave a bridge route
-- statement:
--   For a finite planar graph and vertices in different connected components, choose a planar drawing and a simple curve joining them whose interior avoids all vertices and whose intersections with existing edges occur only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hnot : ¬ G.Reachable u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (gamma : ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ a b, a < b → G.Adj a b →
          ContinuousOn (arc a b) (Set.Icc 0 1) ∧
          Set.InjOn (arc a b) (Set.Icc 0 1) ∧
          arc a b 0 = p a ∧ arc a b 1 = p b ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
        (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
          (a, b) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc a b t = arc c d s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
        Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
        gamma 0 = p u ∧ gamma 1 = p v ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
        (∀ a b, a < b → G.Adj a b →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            gamma t = arc a b s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) := by sorry
