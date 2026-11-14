-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_sequential_phase_bound
-- name    : ZeroFreeRRG.Hardcore.sequential_phase_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:13:55.647309+00:00
-- url     : https://prove2.me/theorems/2ba4cc4b-4452-44c7-9df8-7433f47a1bd0
-- title:
--   Triangle inequality along a finite complex chain
-- statement:
--   If consecutive complex numbers in a chain of length $n$ differ by at most $r$, the endpoints differ by at most $nr$.
-- source:
--   Auxiliary phase estimate for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.sequential_phase_bound (f : ℕ → ℂ) (n : ℕ) (r : ℝ)
    (hstep : ∀ k < n, ‖f k - f (k+1)‖ ≤ r) :
    ‖f 0 - f n‖ ≤ n*r := by sorry
