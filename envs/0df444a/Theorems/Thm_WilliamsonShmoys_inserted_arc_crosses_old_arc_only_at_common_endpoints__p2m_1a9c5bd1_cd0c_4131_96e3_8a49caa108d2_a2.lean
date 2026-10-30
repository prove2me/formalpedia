-- Prove2me | Theorems.Thm_WilliamsonShmoys_inserted_arc_crosses_old_arc_only_at_common_endpoints__p2m_1a9c5bd1_cd0c_4131_96e3_8a49caa108d2_a2
-- name    : WilliamsonShmoys.inserted_arc_crosses_old_arc_only_at_common_endpoints__p2m_1a9c5bd1_cd0c_4131_96e3_8a49caa108d2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:09.48924+00:00
-- url     : https://prove2.me/theorems/e6166acf-8ae9-4caa-9fd9-af658866bc01
-- title:
--   An inserted avoiding arc meets an old edge only at endpoints
-- statement:
--   For an old edge `(a,b)`, any point shared by its arc and the inserted arc has endpoint parameters on both arcs, assuming the inserted arc's interior avoids all vertices and old edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.inserted_arc_crosses_old_arc_only_at_common_endpoints__p2m_1a9c5bd1_cd0c_4131_96e3_8a49caa108d2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v a b : V)
    (gamma : ℝ → ℝ × ℝ) (huv : u < v) (hab : a < b)
    (hp : Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y c d, x < y → c < d → H.Adj x y → H.Adj c d →
        (x, y) ≠ (c, d) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc x y t = arc c d s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s))
    (hAdj : H.Adj a b) (hne : (u, v) ≠ (a, b)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
      gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by sorry
