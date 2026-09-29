-- Prove2me | Theorems.Thm_MarkovMixing_tv_sup_functions
-- name    : MarkovMixing.tv_sup_functions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:15:35.791099+00:00
-- url     : https://prove2.me/theorems/00978d3c-b9ec-47da-b97f-8834f11cc9b8
-- title:
--   Proposition 4.5 -- total variation via bounded test functions
-- statement:
--   Let $\mu$ and $\nu$ be probability distributions on a finite state space $V$, and let $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ denote their **total variation distance**, the largest discrepancy in the probability of a single event. Write $\mathbb E_\mu(f)=\sum_x f(x)\,\mu(x)$ for the expectation of an observable $f:V\to\mathbb R$ under $\mu$.
--
--   The theorem (Proposition 4.5 of Levin–Peres–Wilmer) characterizes the distance by expectations of bounded observables:
--   $$\|\mu-\nu\|_{TV}=\frac12\,\sup_{f:\,\max_x|f(x)|\le1}\bigl|\mathbb E_\mu(f)-\mathbb E_\nu(f)\bigr|,$$
--   the supremum running over all functions $f$ on $V$ bounded by $1$ in absolute value. In words: two distributions are far in total variation exactly when some $[-1,1]$-valued statistic has visibly different means under the two.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.1, Proposition 4.5, p. 49

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Proposition 4.5** (LPW): the total variation distance equals half the
supremum, over functions bounded by `1` in absolute value, of the difference
of expectations. -/
theorem tv_sup_functions {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν =
      2⁻¹ * ⨆ f : {f : V → ℝ // ∀ x, |f x| ≤ 1},
        |∑ x, (f : V → ℝ) x * μ x - ∑ x, (f : V → ℝ) x * ν x| := by
  sorry

end MarkovMixing
