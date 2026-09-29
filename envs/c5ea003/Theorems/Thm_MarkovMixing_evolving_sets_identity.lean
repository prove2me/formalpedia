-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_identity
-- name    : MarkovMixing.evolving_sets_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:49.255191+00:00
-- url     : https://prove2.me/theorems/c4b511c4-603e-44bb-bb5a-645050436ea7
-- title:
--   The evolving-set identity $P^t(x,y)=\frac{\pi(y)}{\pi(x)}\mathbb P_{\{x\}}\{y\in S_t\}$
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with strictly positive stationary distribution $\pi$, and write $Q(S,y)=\sum_{x\in S}\pi(x)P(x,y)$ for the stationary flow from a set $S$ into a state $y$. The **evolving-set process** of Morris and Peres is the Markov chain on subsets of $V$ that, from the current set $S$, draws $u$ uniform on $(0,1]$ and passes to the superlevel set $\{y:Q(S,y)/\pi(y)\ge u\}$; its transition probability from $S$ to $T$ is the length of the interval of thresholds $u$ realizing $T$.
--
--   The theorem (Lemma 17.12 of Levin–Peres–Wilmer) asserts that the set process *contains* the original chain: for all states $x,y$ and every time $t$,
--   $$P^t(x,y)\;=\;\frac{\pi(y)}{\pi(x)}\;\mathbb P_{\{x\}}\bigl\{y\in S_t\bigr\},$$
--   where the right-hand probability is over the evolving-set process started from the singleton $\{x\}$ — the sum of its $t$-step transition probabilities into the sets containing $y$.
--
--   Every question about $t$-step transition probabilities is thereby a question about how the random set grows and shrinks. Combined with the martingale property of $\pi(S_t)$ (the companion lemma), this identity is what converts martingale estimates on sets into the mixing and return-probability bounds of this mission.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 17.4, Lemma 17.12, Eq. (17.14), p. 236

import Definitions.Def_mm_martingale

namespace MarkovMixing

/-- **Lemma 17.12** (LPW): the transition probabilities of the chain are
recovered from the evolving-set process by
`P^t(x,y) = (π(y)/π(x)) P_{{x}}{y ∈ S_t}`. -/
theorem evolving_sets_identity {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (x y : V) (t : ℕ) :
    (P ^ t) x y = π y / π x *
      ∑ T ∈ Finset.univ.filter (fun T : Finset V => y ∈ T),
        ((evolvingSets P π) ^ t) {x} T := by
  sorry

end MarkovMixing
