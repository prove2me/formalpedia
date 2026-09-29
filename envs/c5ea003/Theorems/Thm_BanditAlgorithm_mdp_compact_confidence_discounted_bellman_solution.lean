-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_compact_confidence_discounted_bellman_solution
-- name    : BanditAlgorithm.mdp_compact_confidence_discounted_bellman_solution
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T16:32:21.861284+00:00
-- url     : https://prove2.me/theorems/5c59a6f2-3ea2-426a-a430-6a8cd4fe777c
-- title:
--   Discounted Bellman solution over compact confidence sets
-- statement:
--   Fix $S$ states and $A$ actions, a reward function $r_a(s)\in[0,1]$, and for each state-action pair a nonempty **compact** set $\mathcal C_{s,a}$ of probability vectors on the state space. For every discount factor $\gamma\in[0,1)$ there are a value function $V:\mathcal S\to[0,\tfrac{1}{1-\gamma}]$, an action map $f$ and transition rows $q(s)\in\mathcal C_{s,f(s)}$ such that
--
--   $$
--   r_a(s)+\gamma\langle p, V\rangle \;\le\; V(s)\quad\text{for every action }a\text{ and every }p\in\mathcal C_{s,a},
--   \qquad
--   V(s) \;=\; r_{f(s)}(s)+\gamma\langle q(s), V\rangle .
--   $$
--
--   Together these say that $V$ solves the discounted Bellman optimality equation
--   $V(s)=\max_a\max_{p\in\mathcal C_{s,a}}\big(r_a(s)+\gamma\langle p,V\rangle\big)$ of the *extended* MDP, whose actions are the pairs $(a,p)$ with $p\in\mathcal C_{s,a}$, and that the maximum is attained at $(f(s),q(s))$.
--
--   This is the fixed point computed by the extended value iteration of UCRL2: the confidence sets are the $L^1$ balls around the empirical transition rows, and the extended MDP is the one whose transition matrices range over the confidence region. It is not a finite MDP — its action set is a continuum — so the usual finite-action argument does not apply verbatim.
--
--   What replaces finiteness is compactness. The inner maximisation $\mathrm{opt}(\mathcal C_{s,a}, v)=\max\{\langle p,v\rangle : p\in\mathcal C_{s,a}\}$ is attained because a continuous image of a compact set is a compact set of reals and therefore contains its supremum. Moreover $v\mapsto \mathrm{opt}(\mathcal C_{s,a},v)$ is $1$-Lipschitz for the supremum norm, because every $p\in\mathcal C_{s,a}$ is a probability vector and hence $\langle p,u\rangle\le\langle p,v\rangle+\|u-v\|_\infty$. Consequently the operator $(Tv)(s)=\max_a\big(r_a(s)+\gamma\,\mathrm{opt}(\mathcal C_{s,a},v)\big)$ is a $\gamma$-contraction of $\mathbb R^{\mathcal S}$, and Banach's fixed point theorem supplies $V$; the maximisers over the finite action set and over the compact confidence set supply $f$ and $q$. Evaluating the fixed point equation at a state where $V$ is largest gives $V\le\frac{1}{1-\gamma}$, and at a state where it is smallest gives $V\ge0$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 (extended value iteration in UCRL2); Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 3.1; Puterman, Markov Decision Processes (Wiley 1994), Chapter 6 (the discounted Bellman operator as a contraction).

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

theorem BanditAlgorithm.mdp_compact_confidence_discounted_bellman_solution
    {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hCne : ∀ s a, (C s a).Nonempty)
    (hCcomp : ∀ s a, IsCompact (C s a))
    (hCprob : ∀ s a, ∀ p ∈ C s a, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ (V : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      (∀ s, V s ∈ Set.Icc (0 : ℝ) (1 / (1 - γ))) ∧
      (∀ s a, ∀ p ∈ C s a, r s a + γ * ∑ s', p s' * V s' ≤ V s) ∧
      (∀ s, q s ∈ C s (f s)) ∧
      (∀ s, V s = r s (f s) + γ * ∑ s', q s s' * V s') := by
  sorry
