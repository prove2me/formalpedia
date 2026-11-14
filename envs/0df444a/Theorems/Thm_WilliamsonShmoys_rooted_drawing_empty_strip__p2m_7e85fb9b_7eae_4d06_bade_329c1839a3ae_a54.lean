-- Prove2me | Theorems.Thm_WilliamsonShmoys_rooted_drawing_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a54
-- name    : WilliamsonShmoys.rooted_drawing_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a54
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-13T16:16:01.259689+00:00
-- url     : https://prove2.me/theorems/dc08027d-abcc-463f-b500-8268f72a9ef0
-- title:
--   Redraw separated vertices on opposite sides of an empty strip
-- statement:
--   For a finite planar drawing and two vertices in distinct graph components, construct another drawing with the first vertex at `(0,0)`, the second at `(1,0)`, and all drawn vertices and edge arcs in the half-planes `x ≤ 0` or `x ≥ 1`, preserving the stated injectivity and intersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.rooted_drawing_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a54
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (u v : V) (hsep : ¬ Nonempty (J.Walk u v)) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ a b, a < b → J.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → J.Adj a b → J.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      p u = (0, 0) ∧ p v = (1, 0) ∧
      (∀ w, (p w).1 ≤ 0 ∨ 1 ≤ (p w).1) ∧
      (∀ a b, a < b → J.Adj a b →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (arc a b s).1 ≤ 0 ∨ 1 ≤ (arc a b s).1) := by
  sorry
