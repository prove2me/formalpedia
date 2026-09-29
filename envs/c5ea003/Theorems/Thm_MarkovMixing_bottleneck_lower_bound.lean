-- Prove2me | Theorems.Thm_MarkovMixing_bottleneck_lower_bound
-- name    : MarkovMixing.bottleneck_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:24:52.622681+00:00
-- url     : https://prove2.me/theorems/73ab1957-67bb-47e7-bbaa-19c582b5a5d2
-- title:
--   Theorem 7.3 -- the bottleneck ratio bound
-- statement:
--   Let $P$ be an irreducible, aperiodic Markov chain on a finite state space $V$ with stationary distribution $\pi$. The **edge measure** $Q(x,y)=\pi(x)P(x,y)$ is the stationary flow along $(x,y)$; the **bottleneck ratio** of a set of states $S$ is
--   $$\Phi(S)=\frac{Q(S,S^c)}{\pi(S)}=\frac{\sum_{x\in S}\sum_{y\notin S}\pi(x)P(x,y)}{\pi(S)},$$
--   the conditional probability at stationarity of escaping $S$ in one step; and the **bottleneck constant** is $\Phi_\star=\min\{\Phi(S):\varnothing\ne S,\ \pi(S)\le\tfrac12\}$. The **mixing time** $t_{\mathrm{mix}}$ is the first $t$ at which $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\tfrac14$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ the total variation distance.
--
--   The theorem (Theorem 7.3 of Levin–Peres–Wilmer, the capstone of Chapter 7) asserts:
--   $$t_{\mathrm{mix}}\;\ge\;\frac{1}{4\,\Phi_\star}.$$
--   A chain with a bottleneck — a half-space it leaves only reluctantly — mixes slowly: started inside such a set, the chain needs order $1/\Phi(S)$ steps to transfer the requisite mass out. This is the qualitative converse of the Cheeger inequality of Mission VII.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.2, Theorem 7.3, p. 89

import Definitions.Def_mm_lower

namespace MarkovMixing

/-- **Theorem 7.3** (LPW), the bottleneck-ratio bound and capstone of
Chapter 7: `t_mix ≥ 1/(4 Φ⋆)`. -/
theorem bottleneck_lower_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) :
    (4 * bottleneckStar P π)⁻¹ ≤ (tMix P π : ℝ) := by
  sorry

end MarkovMixing
