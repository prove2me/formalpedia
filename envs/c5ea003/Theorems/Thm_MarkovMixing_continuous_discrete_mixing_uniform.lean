-- Prove2me | Theorems.Thm_MarkovMixing_continuous_discrete_mixing_uniform
-- name    : MarkovMixing.continuous_discrete_mixing_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T23:31:38.790299+00:00
-- url     : https://prove2.me/theorems/eada9c30-53b6-4ca3-93ac-5972ee5ab612
-- title:
--   Theorem 20.3 -- lazy chain versus continuous time, uniformly in the chain
-- statement:
--   Let $P$ be the transition matrix of a finite irreducible Markov chain (from any state, any other is reachable in some number of steps), with stationary distribution $\pi$; the chain need not be aperiodic or reversible. Two derived chains are compared. The **lazy chain** $\tilde P=\tfrac12(I+P)$ flips a fair coin at each step and moves according to $P$ only on heads. The **continuous-time chain** runs $P$ at the jump times of a rate-one Poisson process; its transition kernel is the **heat kernel**
--   $$H_t(x,y)=\sum_{k\ge0}e^{-t}\frac{t^k}{k!}\,P^k(x,y),$$
--   the law of the chain after a Poisson$(t)$ number of steps. Distances to equilibrium are measured in total variation, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 20.3 of Levin–Peres–Wilmer) asserts that the two clocks agree up to a bounded factor, with thresholds that **depend on the accuracy alone and not on the chain**. Fix $\varepsilon>0$. Then:
--
--   1. there is a $K$ such that for *every* finite irreducible chain, every $k\ge K$ and every state $x$: $\|\tilde P^{\,k}(x,\cdot)-\pi\|_{TV}<\varepsilon$ implies $\|H_k(x,\cdot)-\pi\|_{TV}<2\varepsilon$;
--   2. there is an $M$ such that for *every* finite irreducible chain, every $m\ge M$ and every state $x$: $\|H_m(x,\cdot)-\pi\|_{TV}<\varepsilon$ implies $\|\tilde P^{\,4m}(x,\cdot)-\pi\|_{TV}<2\varepsilon$.
--
--   This is the bridge between the discrete and continuous theories, and the reason a mixing bound proved on one side transfers to the other with only a constant factor lost. Part (2) is the harder half: it rests on Lemma 20.4, the statement that a binomial $(4m,\tfrac12)$ variable and $m+{}$Poisson$(m)$ merge in total variation as $m\to\infty$ — the two clocks can be coupled, since both have mean $2m$ and variance $m$.
--
--   *A note on the order of the quantifiers.* The thresholds are quantified **before** the chain. LPW say "for sufficiently large $k$", and their proof delivers exactly that reading: the error in (2) is the total variation distance between the two clock distributions, a quantity that does not see the chain at all, and the estimate behind (1) is $\mathbb P\{N_{2k}<k\}\to0$ for a Poisson process. If instead the threshold may be chosen after the chain, the statement says nothing: for a fixed finite irreducible chain both $\|H_t(x,\cdot)-\pi\|_{TV}$ and $\|\tilde P^{\,t}(x,\cdot)-\pi\|_{TV}$ tend to $0$, so any sufficiently large threshold makes each conclusion true outright and the hypothesis of the implication is never used — the two halves then reduce to the convergence theorem, and the constants $4$ and $2\varepsilon$ could be replaced by anything. Quantified as above the shortcut disappears, because mixing times are unbounded across the family of finite chains and no single threshold can be read off any one of them. Chains are taken on the state spaces $\{0,1,\dots,n-1\}$, which costs nothing since every finite state space is in bijection with one.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 20.2, Theorem 20.3, p. 266

import Definitions.Def_mm_continuous

namespace MarkovMixing

/-- **Theorem 20.3** (LPW): the discrete lazy chain and the continuous-time
chain mix at comparable times.  For every `ε > 0` there is a threshold `K`,
*depending on `ε` alone*, such that for every finite irreducible chain: for
`k ≥ K`, `‖P̃^k(x,·) − π‖ < ε` implies `‖H_k(x,·) − π‖ < 2ε`; and there is a
threshold `M`, again depending on `ε` alone, such that for `m ≥ M`,
`‖H_m(x,·) − π‖ < ε` implies `‖P̃^{4m}(x,·) − π‖ < 2ε`.

The thresholds are quantified before the chain.  LPW say "for sufficiently
large `k`", and their proof produces a bound that does not see the chain at
all: part (ii) rests on Lemma 20.4, the statement that binomial `(4m,1/2)`
and `m +` Poisson `(m)` merge in total variation, a fact about the two clocks
and nothing else; part (i) rests on `P{N_{2k} < k} → 0` for `N` Poisson.  If
instead the threshold may be chosen after the chain, the statement collapses:
both `d^cont(t)` and the distance of the lazy chain tend to `0` for a fixed
irreducible chain, so any large enough threshold makes the conclusion hold
outright and the hypothesis is never read.  Quantified as here, no single
threshold can be read off one chain, because mixing times are unbounded over
the family, and the Binomial--Poisson comparison is forced.

Chains are taken on `Fin n`, which is no loss: every finite state space is in
bijection with one, and the thresholds are what the statement is about. -/
theorem continuous_discrete_mixing_uniform (ε : ℝ) (hε : 0 < ε) :
    (∃ K : ℕ, ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), IsStochastic P →
      Irreducible P → ∀ π : Fin n → ℝ, IsStationary P π →
      ∀ k : ℕ, K ≤ k → ∀ x : Fin n,
        tvDist (rowDist (lazy P) k x) π < ε →
          tvDist (fun y => heatKernel P k x y) π < 2 * ε) ∧
    (∃ M : ℕ, ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), IsStochastic P →
      Irreducible P → ∀ π : Fin n → ℝ, IsStationary P π →
      ∀ m : ℕ, M ≤ m → ∀ x : Fin n,
        tvDist (fun y => heatKernel P m x y) π < ε →
          tvDist (rowDist (lazy P) (4 * m) x) π < 2 * ε) := by
  sorry

end MarkovMixing
