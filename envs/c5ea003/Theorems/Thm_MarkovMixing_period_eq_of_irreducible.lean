-- Prove2me | Theorems.Thm_MarkovMixing_period_eq_of_irreducible
-- name    : MarkovMixing.period_eq_of_irreducible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:41:41.999131+00:00
-- url     : https://prove2.me/theorems/9d582619-1e52-47c9-9bdd-c57462cae471
-- title:
--   Lemma 1.6 -- the period is constant on an irreducible chain
-- statement:
--   For a stochastic irreducible matrix $P$ on a finite state space, all states have the same period: $\gcd\{t\ge1:P^t(x,x)>0\}=\gcd\{t\ge1:P^t(y,y)>0\}$ for all $x,y$. (The period is encoded as the largest common divisor of the return-time set, which equals the gcd when the return set is nonempty -- as irreducibility and stochasticity guarantee.) This makes the period of the chain well defined.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.3, Lemma 1.6, p. 8

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Lemma 1.6** (LPW): for an irreducible chain, all states have the same
period, so the period of the chain is well defined. -/
theorem period_eq_of_irreducible {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P) (x y : V) :
    period P x = period P y := by
  sorry

end MarkovMixing
