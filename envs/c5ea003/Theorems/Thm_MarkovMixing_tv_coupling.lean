-- Prove2me | Theorems.Thm_MarkovMixing_tv_coupling
-- name    : MarkovMixing.tv_coupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:15:50.595371+00:00
-- url     : https://prove2.me/theorems/8040f569-4122-441f-acfe-8e07ba820cff
-- title:
--   Proposition 4.7 -- the coupling characterization of total variation
-- statement:
--   Let $\mu$ and $\nu$ be probability distributions on a finite state space $V$, and let $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ denote their **total variation distance**. A **coupling** of $\mu$ and $\nu$ is a probability distribution $q$ on ordered pairs $V\times V$ whose marginals are $\mu$ and $\nu$ — that is, $\sum_y q(x,y)=\mu(x)$ for every $x$ and $\sum_x q(x,y)=\nu(y)$ for every $y$; one thinks of $q$ as the joint law of a pair of random variables $(X,Y)$ with $X\sim\mu$ and $Y\sim\nu$.
--
--   The theorem (Proposition 4.7 and Remark 4.8 of Levin–Peres–Wilmer) asserts two things. First, every coupling $q$ places at least $\|\mu-\nu\|_{TV}$ of its mass off the diagonal:
--   $$\|\mu-\nu\|_{TV}\;\le\;\sum_{(x,y):\,x\ne y}q(x,y)\;=\;\mathbb P\{X\ne Y\}.$$
--   Second, some coupling attains this bound — an **optimal coupling**, whose off-diagonal mass is exactly $\|\mu-\nu\|_{TV}$. Together: the total variation distance is the minimal probability of disagreement achievable by any joint realization of the two distributions, and the minimum is attained.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.2, Proposition 4.7 and Remark 4.8, pp. 50-51

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Proposition 4.7 and Remark 4.8** (LPW): every coupling `(X,Y)` of `μ`
and `ν` has `P{X ≠ Y} ≥ ‖μ − ν‖_TV`, and there is an *optimal* coupling
attaining equality. -/
theorem tv_coupling {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    (∀ q : V × V → ℝ, IsCoupling μ ν q →
      tvDist μ ν ≤ ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p) ∧
    ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      tvDist μ ν = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p := by
  sorry

end MarkovMixing
