-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_stationary_vanishes_off_recurrent
-- name    : YoungConventions.Perturbed.stationary_vanishes_off_recurrent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:23.504527+00:00
-- url     : https://prove2.me/theorems/16032c2a-91f9-44a9-a068-70a11f8c4682
-- title:
--   A stationary distribution of a finite chain vanishes off the recurrent states (p. 80)
-- statement:
--   Let $A$ be a Markov chain on a finite set $X$, let $\nu$ be a stationary distribution of $A$, and let $z \in X$ be a state that is not recurrent under $A$ (some state reachable from $z$ cannot reach $z$). Then
--   $$\nu_z = 0.$$
--
--   In the proof of Theorem 4 this is applied to the limit $\mu^0$ and the unperturbed chain $P^0$: the stochastically stable states lie in the recurrent classes of $P^0$, so the potential only needs to be computed on recurrent states.
--
--   **Formalization Note** The page states the fact for $\mu^0$ and $P^0$; it is stated here for an arbitrary finite chain and an arbitrary stationary distribution.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 80 (PDF p. 25), after the proof of Lemma 1

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain

namespace YoungConventions.Perturbed

/-- Stationary distributions vanish off the recurrent states (Young 1993, Econometrica 61:57–84,
Appendix, p. 80, PDF p. 25: "Since μ⁰ is a stationary distribution of P⁰, μ⁰_z = 0 for every
state z that is not recurrent under P⁰").

For every Markov chain `A` on a finite set `X`, every stationary distribution `ν` of `A` and
every state `z` that is not recurrent under `A`, `ν z = 0`.

**Formalization Note.** The page applies this to `μ⁰` and `P⁰`; it is stated here for an arbitrary
finite chain, which is the fact used. -/
theorem stationary_vanishes_off_recurrent {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (ν : X → ℝ) (hν : IsStationaryDist A ν) (z : X) (hz : ¬ IsRecurrentState A z) :
    ν z = 0 := by sorry

end YoungConventions.Perturbed
