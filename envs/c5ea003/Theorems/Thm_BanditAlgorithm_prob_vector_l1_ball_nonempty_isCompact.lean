-- Prove2me | Theorems.Thm_BanditAlgorithm_prob_vector_l1_ball_nonempty_isCompact
-- name    : BanditAlgorithm.prob_vector_l1_ball_nonempty_isCompact
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T16:35:54.444979+00:00
-- url     : https://prove2.me/theorems/c8507112-dcb2-438b-aa36-c4658ae30343
-- title:
--   An $\ell_1$ ball of probability vectors is nonempty and compact
-- statement:
--   Let $c$ be a probability vector on a finite set $\iota$ and let $\beta\ge0$. Then the set
--
--   $$\mathcal C=\Big\{p:\iota\to\mathbb R \;\Big|\; p\ge 0,\ \sum_i p_i=1,\ \sum_i |p_i-c_i|\le\beta\Big\}$$
--
--   of probability vectors within $L^1$ distance $\beta$ of $c$ is nonempty and compact.
--
--   This is the confidence set used by UCRL2: $c$ is the empirical transition row $\hat P_a(s)$ and $\beta$ the confidence radius supplied by Weissman's inequality. Nonemptiness and compactness are exactly the hypotheses under which the extended MDP — whose actions are the pairs (action, transition row in the confidence set) — has a solution of its Bellman optimality equation, so this lemma is what connects the statistical part of the analysis to the planning part.
--
--   Nonemptiness holds because $c$ itself lies in $\mathcal C$. For compactness, note first that $\mathcal C$ is contained in the cube $[0,1]^{\iota}$: each coordinate is nonnegative and, being one term of a sum of nonnegative numbers equal to $1$, is at most $1$. The cube is compact by Tychonoff's theorem. Finally $\mathcal C$ is closed, being the intersection of the closed sets $\{p : p_i \ge 0\}$, the level set $\{p : \sum_i p_i = 1\}$ and the sublevel set $\{p : \sum_i |p_i - c_i| \le \beta\}$, all closed because the coordinate projections, and hence the finite sums and absolute values built from them, are continuous. A closed subset of a compact set is compact.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 (the confidence set of UCRL2 and its extended MDP); Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 3 (Eq. (3) and Figure 2).

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem BanditAlgorithm.prob_vector_l1_ball_nonempty_isCompact
    {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∑ i, c i = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β) ∧
      IsCompact {p : ι → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∑ i, |p i - c i| ≤ β} := by
  sorry
