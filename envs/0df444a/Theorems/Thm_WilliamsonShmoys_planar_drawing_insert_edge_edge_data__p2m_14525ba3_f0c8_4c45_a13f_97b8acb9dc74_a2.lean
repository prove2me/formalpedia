-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_insert_edge_edge_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
-- name    : WilliamsonShmoys.planar_drawing_insert_edge_edge_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:53.134959+00:00
-- url     : https://prove2.me/theorems/a0e544ef-f869-4e4f-a6fb-1e2f695a765f
-- title:
--   Edge data for inserting an avoiding arc
-- statement:
--   For each increasing ordered edge of the enlarged graph, the patched arc is continuous and injective on the unit interval, has the prescribed endpoint values, and has strict interior disjoint from all vertex points.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_insert_edge_edge_data__p2m_14525ba3_f0c8_4c45_a13f_97b8acb9dc74_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V)
    (gamma : ℝ → ℝ × ℝ) (huv : u < v)
    (hp : Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧
      Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y →
        ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s))
    (hchar : ∀ x y, G.Adj x y ↔
      H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u))
    (arcNew : V → V → ℝ → ℝ × ℝ)
    (hpatch : ∀ x y t, arcNew x y t =
      if x = u ∧ y = v then gamma t else arc x y t) :
    ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arcNew x y) (Set.Icc 0 1) ∧
      Set.InjOn (arcNew x y) (Set.Icc 0 1) ∧
      arcNew x y 0 = p x ∧ arcNew x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arcNew x y t ≠ p w := by sorry
