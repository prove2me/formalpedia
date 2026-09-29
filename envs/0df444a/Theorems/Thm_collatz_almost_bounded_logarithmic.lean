-- Prove2me | Theorems.Thm_collatz_almost_bounded_logarithmic
-- name    : collatz_almost_bounded_logarithmic
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T05:09:30.778062+00:00
-- url     : https://prove2.me/theorems/8469bda5-b114-46bd-9a75-5a504e93b336
-- title:
--   Tao Theorem 1.3: almost all Collatz orbits attain almost bounded values
-- statement:
--   For every real-valued function f tending to infinity on positive integer inputs, the positive inputs n whose Collatz orbit contains a value strictly below f(n) form a set of logarithmic density one. The real-cutoff reciprocal mass is normalized by log x; the full orbit includes its starting value. This is not natural density, a fixed absolute bound, or convergence of every orbit to one.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Theorem 1.3. https://arxiv.org/html/1909.03562v7

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_weightedLogMassReal
open Filter
open scoped Topology

theorem collatz_almost_bounded_logarithmic (f : ℕ → ℝ) (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → M < f n) : Tendsto (fun x : ℝ => weightedLogMassReal (fun n => 0 < n) (fun n => ∃ k : ℕ, ((collatzStep^[k] n : ℕ) : ℝ) < f n) (fun n => 1 / (n : ℝ)) x) atTop (𝓝 (1 : ℝ)) := by sorry
