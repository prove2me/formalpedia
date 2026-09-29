-- Prove2me | Theorems.Thm_syracuse_almost_bounded_logarithmic
-- name    : syracuse_almost_bounded_logarithmic
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T03:47:01.085126+00:00
-- url     : https://prove2.me/theorems/6cc34b4a-20fb-4dc1-8e72-685a19c096d1
-- title:
--   Tao Theorem 1.6: almost all Syracuse orbits attain almost bounded values
-- statement:
--   For every real-valued function f tending to infinity along the positive odd integers, the set of positive odd inputs n whose Syracuse orbit contains a value strictly below f(n) has logarithmic density one half. Equivalently, the property holds for almost all odd inputs in the logarithmic sense. Cutoffs are real, the full orbit includes its initial value, and f is unrestricted off the positive odd domain. This is not convergence of every orbit, a fixed absolute bound, or a natural-density assertion.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7 (16 July 2026), Theorem 1.6 and the immediately preceding logarithmic-density convention. https://arxiv.org/html/1909.03562v7

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin
open Filter
open scoped Topology

theorem syracuse_almost_bounded_logarithmic (f : ℕ → ℝ) (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < n ∧ Odd n) → M < f n) : Tendsto (fun x : ℝ => weightedLogMassReal (fun n => 0 < n ∧ Odd n) (fun n => ∃ k : ℕ, ((syracuseStep^[k] n : ℕ) : ℝ) < f n) (fun n => 1 / (n : ℝ)) x) atTop (𝓝 (1 / 2 : ℝ)) := by sorry
