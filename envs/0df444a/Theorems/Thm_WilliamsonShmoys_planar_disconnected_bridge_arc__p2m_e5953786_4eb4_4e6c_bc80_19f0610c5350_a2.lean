-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
-- name    : WilliamsonShmoys.planar_disconnected_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:52.562019+00:00
-- url     : https://prove2.me/theorems/6de859ac-ad77-458f-9e8d-992385bc18db
-- title:
--   Find an admissible bridge arc between planar components
-- statement:
--   From a planar drawing of a disconnected graph, choose two vertices in different components and a simple curve between their drawing points whose interior avoids all drawn vertices and whose intersections with existing edges occur only at allowed endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V)
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hnot : ¬ G.Connected) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ u v, u < v → G.Adj u v →
          ContinuousOn (arc u v) (Set.Icc 0 1) ∧
          Set.InjOn (arc u v) (Set.Icc 0 1) ∧
          arc u v 0 = p u ∧ arc u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
        (∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      ∃ u v : V, u < v ∧ ¬ G.Reachable u v ∧
        ∃ c : ℝ → ℝ × ℝ,
          ContinuousOn c (Set.Icc 0 1) ∧
          Set.InjOn c (Set.Icc 0 1) ∧
          c 0 = p u ∧ c 1 = p v ∧
          (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
          (∀ x y, x < y → G.Adj x y →
            ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
              c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
