-- Prove2me | Theorems.Thm_syracuse_uniform_logarithmic_tail_bound
-- name    : syracuse_uniform_logarithmic_tail_bound
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T02:54:33.727347+00:00
-- url     : https://prove2.me/theorems/da8b1c33-12f2-4cb8-afe5-7944f81c1706
-- title:
--   Tao Theorem 3.1: uniform logarithmic tail bound for Syracuse orbit minima
-- statement:
--   There are absolute positive constants C and c such that, for every real threshold M at least two and every real cutoff x at least two, the sum of 1/n over positive odd integers n at most x whose full Syracuse orbit minimum exceeds M, divided by log x, is at most C/(log M)^c. Both constants are independent of M and x. The orbit includes its initial value. This is the uniform exceptional-sum assertion in Tao's Theorem 3.1; its proof remains open in this formalization project.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7 (16 July 2026), Theorem 3.1, first displayed estimate. https://arxiv.org/html/1909.03562v7

import Mathlib
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin

theorem syracuse_uniform_logarithmic_tail_bound : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 2 ≤ M → 2 ≤ x → weightedLogMassReal (fun n => 0 < n ∧ Odd n) (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x ≤ C / Real.rpow (Real.log M) c := by sorry
