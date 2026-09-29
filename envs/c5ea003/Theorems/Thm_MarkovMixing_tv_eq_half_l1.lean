-- Prove2me | Theorems.Thm_MarkovMixing_tv_eq_half_l1
-- name    : MarkovMixing.tv_eq_half_l1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:15:21.474297+00:00
-- url     : https://prove2.me/theorems/bfad9713-bd4c-4c03-8aef-16ccacf2b6b7
-- title:
--   Proposition 4.2 -- total variation as half the $\ell^1$ distance
-- statement:
--   Let $\mu$ and $\nu$ be probability distributions on a finite state space $V$, and let
--   $$\|\mu-\nu\|_{TV}=\max_{A\subseteq V}\bigl|\mu(A)-\nu(A)\bigr|$$
--   denote their **total variation distance** — the largest discrepancy the two distributions assign to a single event.
--
--   The theorem gives the two standard closed forms for this distance (Proposition 4.2 and Remark 4.3 of Levin–Peres–Wilmer). First, it is half the $\ell^1$ distance between the mass functions:
--   $$\|\mu-\nu\|_{TV}=\frac12\sum_{x\in V}\bigl|\mu(x)-\nu(x)\bigr|.$$
--   Second, it equals the total excess of $\mu$ over $\nu$ on the set where $\mu$ dominates:
--   $$\|\mu-\nu\|_{TV}=\sum_{x:\,\mu(x)\ge\nu(x)}\bigl(\mu(x)-\nu(x)\bigr),$$
--   i.e. the maximum in the definition is attained at the event $\{x:\mu(x)\ge\nu(x)\}$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.1, Proposition 4.2 and Remark 4.3, p. 48

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Proposition 4.2 and Remark 4.3** (LPW): the total variation distance is
half the `ℓ¹` distance, and equals the excess of `μ` over `ν` on the set
where `μ ≥ ν`. -/
theorem tv_eq_half_l1 {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν = 2⁻¹ * ∑ x, |μ x - ν x| ∧
    tvDist μ ν = ∑ x ∈ Finset.univ.filter (fun x : V => ν x ≤ μ x), (μ x - ν x) := by
  sorry

end MarkovMixing
