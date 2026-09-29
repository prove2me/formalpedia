-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ucb_index_exponential_sum_bound
-- name    : BanditAlgorithm.bandit_ucb_index_exponential_sum_bound
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-19T05:19:13.179752+00:00
-- url     : https://prove2.me/theorems/803beaef-91c9-4910-8330-f2bc4ff33a7b
-- title:
--   Lemma 8.2 exponential-sum bound
-- statement:
--   For $n\in\mathbb{N}$, $\varepsilon>0$, and $a>0$, split the Lemma 8.2 index-count sum at $u=2a/\varepsilon^2$. Bound each pre-cutoff term by $1$ and each post-cutoff term by $\exp(-[t(\varepsilon-\sqrt{2a/t})]^2/(2t))$. The resulting finite sum is at most $1+\frac{2}{\varepsilon^2}(a+\sqrt{\pi a}+1)$. This is the deterministic sum-to-integral and Gaussian-calculus stage of the source proof.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Lemma 8.2 proof, printed pp. 118-119 / PDF pp. 127-128: cutoff u = 2a ε^-2, Corollary 5.5 exponential sum, comparison with the displayed improper integral, and substitution s = ε sqrt(t) - sqrt(2a).

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory ProbabilityTheory Real

namespace BanditAlgorithm

theorem bandit_ucb_index_exponential_sum_bound
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∑ t ∈ Finset.Icc 1 n,
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
          ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      1 + 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  sorry

end BanditAlgorithm
