-- Prove2me | Theorems.Thm_MarkovMixing_optional_stopping
-- name    : MarkovMixing.optional_stopping
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:19.13777+00:00
-- url     : https://prove2.me/theorems/0dbc4c64-f45e-427b-b528-a42c33084b24
-- title:
--   Optional Stopping Theorem
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$. A **martingale adapted to the chain** is a family $M_t$ of real-valued functions of the trajectory up to time $t$ whose one-step conditional expectation is neutral: $\sum_yP(\omega_t,y)\,M_{t+1}(\omega,y)=M_t(\omega)$ for every trajectory $\omega$, where $(\omega,y)$ extends $\omega$ by one step. A **stopping time** $\tau$ is a $\{0,1\}$-valued stopping rule: whether to stop at time $t$ is determined by the trajectory up to $t$. Fix a starting state $x$; $\tau$ is **almost surely finite** when the total probability of ever stopping equals one, and the **stopped expectation** $\mathbb E_x(M_\tau)$ is the sum over all times $t$ and trajectories from $x$ of (trajectory weight) × (probability of stopping exactly at $t$) × $M_t$.
--
--   The theorem (the **Optional Stopping Theorem**, Corollary 17.7 of Levin–Peres–Wilmer) asserts: if $M$ is uniformly bounded — $|M_t(\omega)|\le K$ for some constant $K$ and all $t,\omega$ — and $\tau$ is almost surely finite, then
--   $$\mathbb E_x\bigl(M_{\tau}\bigr)\;=\;M_0(x):$$
--   stopping a fair game at a fair time wins nothing. This identity is the workhorse of discrete probability — the gambler's ruin probabilities and hitting-time identities of Missions I and VI are all instances — and in this mission it feeds the analysis of the evolving-set process.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 17.2, Corollary 17.7 (Optional Stopping Theorem, Version 2), p. 232

import Definitions.Def_mm_martingale

namespace MarkovMixing

/-- **Corollary 17.7, the Optional Stopping Theorem** (LPW): if `M` is a
bounded martingale with respect to the chain and `τ` is an almost surely
finite stopping time, then `E_x(M_τ) = M_0(x)`. -/
theorem optional_stopping {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (M : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (hM : IsChainMartingale P M)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (hs01 : ∀ (t : ℕ) (ω : Fin (t + 1) → V), s t ω = 0 ∨ s t ω = 1)
    (x : V) (hfin : (∑' t : ℕ, ∑ y, stopAtProb P x s t y) = 1)
    (K : ℝ) (hK : ∀ (t : ℕ) (ω : Fin (t + 1) → V), |M t ω| ≤ K) :
    stoppedExp P x s M = M 0 (fun _ => x) := by
  sorry

end MarkovMixing
