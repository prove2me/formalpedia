-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3
-- name    : WilliamsonShmoys.planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:18.137454+00:00
-- url     : https://prove2.me/theorems/b17ceb0c-ef48-4b04-b3c0-3db1e5f6161d
-- title:
--   Augment a disconnected plane drawing by an edge between components
-- statement:
--   Extend the drawing by one edge joining vertices in different connected components, preserving the original drawing and ensuring the extended drawing remains planar under the given arc conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_disconnected_path_augmentation__p2m_100679c8_dd25_4620_924f_9d4949429e29_a3 {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hCross : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hG_not_connected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, ∃ q : V → V → ℝ → ℝ × ℝ, ∃ u v,
      G ≤ H ∧ u < v ∧ ¬ G.Reachable u v ∧ H.Adj u v ∧ ¬ G.Adj u v ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (q x y) (Set.Icc 0 1) ∧
        Set.InjOn (q x y) (Set.Icc 0 1) ∧
        q x y 0 = p x ∧ q x y 1 = p y ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, q x y t ≠ p w) ∧
        (∀ a b, a < b → H.Adj a b → (x, y) ≠ (a, b) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            q x y t = q a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, q x y t = arc x y t) := by sorry
