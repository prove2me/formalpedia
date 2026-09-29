-- Prove2me | Theorems.Thm_syracuse_almost_bounded_of_log_tail
-- name    : syracuse_almost_bounded_of_log_tail
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T02:51:33.940402+00:00
-- url     : https://prove2.me/theorems/c754f5b7-fdc5-4030-bf47-635c5ba72bc1
-- title:
--   Syracuse almost-boundedness from a uniform logarithmic tail bound
-- statement:
--   Assume positive constants C and c give a uniform bound C/(log M)^c for the normalized harmonic mass of positive odd inputs whose Syracuse orbit minimum exceeds M, for all integer thresholds M and cutoffs x at least two. For every real-valued function f on natural numbers tending to infinity, the normalized harmonic mass of positive odd inputs n for which no Syracuse iterate is strictly below f(n) then tends to zero. The orbit includes its initial value. This is a conditional deduction: the analytic tail bound remains a hypothesis. Cutoffs here are integers and the conclusion is ambient exceptional mass zero, without a separate relative-density normalization claim.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 3, deduction of Theorem 1.6 from Theorem 3.1. https://arxiv.org/html/1909.03562v7 . This conditional formalization uses the integer-parameter specialization of the tail bound and an ambient exceptional-mass conclusion; it is not the full unconditional Theorem 1.6.

import Mathlib
import Definitions.Def_weightedLogMass
import Definitions.Def_syracuseOrbitMin
open Filter
open scoped Topology

theorem syracuse_almost_bounded_of_log_tail (f : ℕ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (hbound : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x → weightedLogMass (fun n => 0 < n ∧ Odd n) (fun n => (M : ℝ) < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x ≤ C / Real.rpow (Real.log (M : ℝ)) c) (hf : Tendsto f atTop atTop) : Tendsto (fun x : ℕ => weightedLogMass (fun n => 0 < n ∧ Odd n) (fun n => ¬ ∃ k : ℕ, ((syracuseStep^[k] n : ℕ) : ℝ) < f n) (fun n => 1 / (n : ℝ)) x) atTop (𝓝 0) := by sorry
