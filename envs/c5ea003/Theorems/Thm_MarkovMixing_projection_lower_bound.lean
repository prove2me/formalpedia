-- Prove2me | Theorems.Thm_MarkovMixing_projection_lower_bound
-- name    : MarkovMixing.projection_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:25:22.334652+00:00
-- url     : https://prove2.me/theorems/7c0a39ed-0ec8-4e9c-8592-f69a603ee86d
-- title:
--   Lemma 7.9 -- projections do not increase total variation
-- statement:
--   Let $\mu$ and $\nu$ be probability distributions on a finite state space $V$, let $f:V\to\Lambda$ be any map to a finite set $\Lambda$, and write $f_*\mu$ for the **pushforward** of $\mu$ along $f$ — the law of the statistic, $(f_*\mu)(b)=\sum_{a:f(a)=b}\mu(a)$. Let $\|\mu-\nu\|_{TV}=\max_{A}|\mu(A)-\nu(A)|$ denote the total variation distance (on $V$ or on $\Lambda$ as appropriate).
--
--   The theorem (Lemma 7.9 of Levin–Peres–Wilmer) asserts that projecting can only lose information:
--   $$\bigl\|f_*\mu-f_*\nu\bigr\|_{TV}\;\le\;\|\mu-\nu\|_{TV}.$$
--   Consequently any lower bound on the distance between the projected laws — for instance one produced by the distinguishing-statistic inequality applied on $\Lambda$ — is automatically a lower bound on the distance between the original distributions. This is the step that turns observable-level separations into total-variation lower bounds for chains.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.3, Lemma 7.9, pp. 92-93

import Definitions.Def_mm_lower

namespace MarkovMixing

/-- **Lemma 7.9** (LPW): projecting by a statistic `f : Ω → Λ` can only
decrease total variation distance:
`‖μ f⁻¹ − ν f⁻¹‖_TV ≤ ‖μ − ν‖_TV`. -/
theorem projection_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) (f : V → Λ) :
    tvDist (pushforward μ f) (pushforward ν f) ≤ tvDist μ ν := by
  sorry

end MarkovMixing
