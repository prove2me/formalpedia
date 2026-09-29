-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_mixing
-- name    : MarkovMixing.evolving_sets_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:32.450327+00:00
-- url     : https://prove2.me/theorems/6e6862c3-cf73-4aee-89dc-edab1af3f858
-- title:
--   Evolving-set mixing bound (Morris--Peres)
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ that is **lazy** — $P(x,x)\ge\tfrac12$ at every state — with stationary distribution $\pi$; write $\pi_{\min}=\min_x\pi(x)$. Reversibility is **not** assumed. The **bottleneck constant** (Mission IV) is
--   $$\Phi_\star=\min\Bigl\{\frac{\sum_{x\in S,\,y\notin S}\pi(x)P(x,y)}{\pi(S)}\;:\;\varnothing\ne S\subseteq V,\ \pi(S)\le\tfrac12\Bigr\},$$
--   the worst conditional escape probability of a half-space at stationarity. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Theorem 17.10, Morris–Peres; Levin–Peres–Wilmer — the capstone of Chapter 17) asserts: for every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\Bigl\lceil\frac{2}{\Phi_\star^{2}}\,\log\Bigl(\frac{1}{\varepsilon\,\pi_{\min}}\Bigr)\Bigr\rceil$$
--   (the ceiling absorbs the rounding of the real-valued bound to an integer time).
--
--   For reversible chains this recovers the Cheeger-route bound of Mission VII — but no reversibility is needed, which is the theorem's point: geometry controls mixing for *every* lazy chain. The proof analyzes the evolving-set process of this mission: laziness keeps the thresholds tame, the bottleneck constant forces a per-step multiplicative decay of $\mathbb E\sqrt{\pi(S_t)(1-\pi(S_t))}$, and the identity $P^t(x,y)=\tfrac{\pi(y)}{\pi(x)}\mathbb P_{\{x\}}\{y\in S_t\}$ converts that decay into total-variation mixing.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 17.4, Theorem 17.10, p. 235

import Definitions.Def_mm_martingale
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 17.10** (Morris–Peres; LPW), the capstone of Chapter 17: for a
lazy irreducible chain (no reversibility required!),
`t_mix(ε) ≤ ⌈(2/Φ⋆²) log(1/(ε π_min))⌉` (the ceiling absorbs
integer rounding). -/
theorem evolving_sets_mixing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x)
    (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime P π ε : ℝ) ≤
      ⌈2 / bottleneckStar P π ^ 2 * Real.log (1 / (ε * ⨅ x : V, π x))⌉₊ := by
  sorry

end MarkovMixing
