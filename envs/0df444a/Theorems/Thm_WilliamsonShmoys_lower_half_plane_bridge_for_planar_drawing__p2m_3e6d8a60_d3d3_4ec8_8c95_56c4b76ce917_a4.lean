-- Prove2me | Theorems.Thm_WilliamsonShmoys_lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
-- name    : WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:17.651181+00:00
-- url     : https://prove2.me/theorems/10be64ac-0b0f-41ef-a1e1-18479b880a3d
-- title:
--   Join two exposed vertices by a straight exterior segment
-- statement:
--   For a drawing with the two selected vertices on the horizontal axis and all other vertices and edge interiors strictly above it, construct the continuous injective horizontal segment between the selected vertices and prove it meets vertices and edges only at allowed endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.lower_half_plane_bridge_for_planar_drawing__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → G.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
        (a, b) ≠ (c, d) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc c d s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    {u v : V}
    (hpu : (p u).2 = 0) (hpv : (p v).2 = 0)
    (hx : (p u).1 < (p v).1)
    (hvertices : ∀ w, w ≠ u → w ≠ v → 0 < (p w).2)
    (harcs : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (arc a b t).2) :
    ∃ gamma : ℝ → ℝ × ℝ,
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ a b, a < b → G.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          gamma t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
