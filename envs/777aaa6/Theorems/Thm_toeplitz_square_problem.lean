-- Prove2me | Theorems.Thm_toeplitz_square_problem
-- name    : toeplitz_square_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T19:14:40.717555+00:00
-- url     : https://prove2.me/theorems/9544a9d2-5c9c-4be7-8102-4abfc206c4a3
-- statement:
--   **Toeplitz' Inscribed Square Problem** (Square Peg Problem): Does every simple closed curve (Jordan curve) in the plane contain the four vertices of a square?
--
--   Proposed by Otto Toeplitz in 1911. Proved for smooth or piecewise-smooth curves, rectifiable curves with various regularity conditions, and locally monotone curves. The general case for arbitrary continuous (Jordan) curves remains open after over 100 years.
--
--   **Source**: Toeplitz, O. (1911). Verhandlungen der Schweizerischen Naturforschenden Gesellschaft. 94, 197. Also: Matschke, B. (2014). A survey on the square peg problem. Notices AMS 61(4), 346–352.
-- source:
--   https://en.wikipedia.org/wiki/Inscribed_square_problem

import Mathlib

theorem toeplitz_square_problem (γ : ℝ → ℝ × ℝ)
    (hγ_cont : Continuous γ)
    (hγ_periodic : ∀ t, γ (t + 1) = γ t)
    (hγ_inj : ∀ s t, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → γ s = γ t → s = t) :
    ∃ t1 t2 t3 t4 : ℝ,
      let p1 := γ t1; let p2 := γ t2; let p3 := γ t3; let p4 := γ t4
      dist p1 p2 = dist p2 p3 ∧
      dist p2 p3 = dist p3 p4 ∧
      dist p3 p4 = dist p4 p1 ∧
      dist p1 p3 = dist p2 p4 ∧
      dist p1 p3 = Real.sqrt 2 * dist p1 p2 := by
  sorry
