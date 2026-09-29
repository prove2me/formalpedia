-- Prove2me | Theorems.Thm_fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
-- name    : fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T08:16:30.020181+00:00
-- url     : https://prove2.me/theorems/c327e7b1-5dbf-4d0f-a202-ff1b7303a992
-- statement:
--   This is the corrected integer-exponent window used in the fixed-matrix sampling moment argument.  Let $n=max(n_1,n_2)$ and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate corresponding to $m$ expected samples.  If the logarithmic scale is nontrivial, $1le etalog n$, and the sample size satisfies
--
--   $$
--   m ge 2,eta,nlog n,
--   $$
--
--   then there is an integer moment exponent $q$ such that
--
--   $$
--   1le q,qquad etalog nle qle 2etalog n,qquad qle pn.
--   $$
--
--   The point of the lemma is the ceiling construction $q=lceil etalog nceil$: the extra factor $2$ in the sample lower bound is exactly what makes the admissibility condition $qle pn$ automatic.  This replaces the earlier node without the two explicit lower-window hypotheses, which is false when $n=1$ and $m=0$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem fixed_matrix_sampling_log_moment_exponent_window_exists_of_two_sample_lower
    (β : ℝ) :
    2 < β →
    ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (1 : ℝ) ≤ β * Real.log (↑(max n₁ n₂)) →
      (m : ℝ) ≥ 2 * β * (↑(max n₁ n₂)) *
        Real.log (↑(max n₁ n₂)) →
      ∃ q : ℕ, 1 ≤ q ∧
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) := by
  sorry
