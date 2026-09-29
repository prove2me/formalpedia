-- Prove2me | Theorems.Thm_MarkovMixing_random_target_lemma
-- name    : MarkovMixing.random_target_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:00:50.035654+00:00
-- url     : https://prove2.me/theorems/51f8717b-0186-4ece-83aa-89cb78c09de4
-- title:
--   Lemma 10.1 -- the random target lemma
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with stationary distribution $\pi$. For states $a$ and $y$, write $\mathbb E_a(\tau_y)$ for the **expected hitting time** of $y$ from $a$ — the expected number of steps for the chain started at $a$ to first reach $y$ (formalized, as throughout this series, by the tail-sum $\sum_{t\ge0}\mathbb P_a\{\tau_y>t\}$).
--
--   The theorem (the **Random Target Lemma**, Lemma 10.1 of Levin–Peres–Wilmer) asserts that the expected time to hit a $\pi$-random target does not depend on the starting state: for any two states $a,b$,
--   $$\sum_{y\in V}\mathbb E_a(\tau_y)\,\pi(y)\;=\;\sum_{y\in V}\mathbb E_b(\tau_y)\,\pi(y).$$
--   Choosing the target according to the stationary distribution erases the advantage of any starting position — a surprising exact identity, proved by observing that the quantity is a harmonic function of the start and hence constant for an irreducible chain.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 10.2, Lemma 10.1, p. 128

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Lemma 10.1, the Random Target Lemma** (LPW): for an irreducible chain
with stationary distribution `π`, the quantity `∑_y E_a(τ_y) π(y)` does not
depend on the starting state `a`. -/
theorem random_target_lemma {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (a b : V) :
    ∑ y, expSetHitTime P a {y} * π y = ∑ y, expSetHitTime P b {y} * π y := by
  sorry

end MarkovMixing
