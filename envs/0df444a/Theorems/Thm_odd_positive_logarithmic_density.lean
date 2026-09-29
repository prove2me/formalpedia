-- Prove2me | Theorems.Thm_odd_positive_logarithmic_density
-- name    : odd_positive_logarithmic_density
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T03:36:05.005686+00:00
-- url     : https://prove2.me/theorems/16b8b15a-4e97-4771-909f-c9009f1e3c8b
-- title:
--   Positive odd integers have logarithmic density one half
-- statement:
--   As a real cutoff x tends to infinity, the sum of 1/n over positive odd integers n at most x, divided by log x, tends to one half. The finite sum includes exactly the natural integers through the floor of x. This is logarithmic density, not a claim about the proportion of integers in an unweighted finite sample.
-- source:
--   Elementary odd-input harmonic normalization used in Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 1, paragraph defining almost all odd inputs immediately before Theorem 1.6. https://arxiv.org/html/1909.03562v7 . The proof uses the odd harmonic-sum identity and the harmonic/logarithm asymptotic; no new named theorem number is attributed to the paper.

import Mathlib
import Definitions.Def_weightedLogMassReal
open Filter
open scoped Topology

theorem odd_positive_logarithmic_density : Tendsto (fun x : ℝ => weightedLogMassReal (fun k => 0 < k ∧ Odd k) (fun _ => True) (fun k => 1 / (k : ℝ)) x) atTop (𝓝 (1 / 2 : ℝ)) := by sorry
