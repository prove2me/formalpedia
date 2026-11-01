-- Prove2me | Theorems.Thm_WilliamsonShmoys_fary_straight_line_drawing__p2m_31b80458_edea_4a06_ad98_a555b209930b_a4
-- name    : WilliamsonShmoys.fary_straight_line_drawing__p2m_31b80458_edea_4a06_ad98_a555b209930b_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:27.175733+00:00
-- url     : https://prove2.me/theorems/17029d20-8d2c-4a35-a93f-3980f965bb39
-- title:
--   Straight-line realization of a planar drawing
-- statement:
--   A graph with the supplied crossing-free drawing has an injective straight-line realization in which no edge contains another vertex in its interior and distinct edges intersect only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.fary_straight_line_drawing__p2m_31b80458_edea_4a06_ad98_a555b209930b_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    WilliamsonShmoys.HasPlanarDrawingOn K →
      ∃ p : V → ℝ × ℝ, Function.Injective p ∧
        (∀ u v w, u < v → K.Adj u v → w ≠ u → w ≠ v →
          ∀ t : ℝ, 0 < t → t < 1 →
            (1 - t) • p u + t • p v ≠ p w) ∧
        (∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
          (u, v) ≠ (x, y) →
          ∀ t s : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ s → s ≤ 1 →
            (1 - t) • p u + t • p v = (1 - s) • p x + s • p y →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
