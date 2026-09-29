-- Prove2me | Theorems.Thm_MarkovMixing_exists_stationary_pos
-- name    : MarkovMixing.exists_stationary_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:11.386079+00:00
-- url     : https://prove2.me/theorems/5dfbfff8-ac04-4b5d-874d-719ec10844eb
-- title:
--   Proposition 1.14 -- existence of a positive stationary distribution
-- statement:
--   An irreducible chain on a finite nonempty state space has a stationary distribution $\pi$ with $\pi(x)>0$ for every state $x$, satisfying moreover $$\pi(x)\,\mathbb{E}_x(\tau_x^+)=1,$$ i.e. $\pi(x)=1/\mathbb{E}_x(\tau_x^+)$ where $\tau_x^+$ is the first return time to $x$. The identity is stated multiplicatively, so a divergent return-time series (which the encoding would send to the junk value $0$) cannot satisfy it vacuously.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.5.3, Proposition 1.14, pp. 12-13

import Definitions.Def_mm_path

namespace MarkovMixing

/-- **Proposition 1.14** (LPW): an irreducible chain has a stationary
distribution `π` with `π(x) > 0` for all `x`, and moreover
`π(x) = 1 / E_x(τ⁺_x)` — stated multiplicatively as
`π(x) · E_x(τ⁺_x) = 1`. -/
theorem exists_stationary_pos {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P) :
    ∃ π : V → ℝ, IsStationary P π ∧ (∀ x : V, 0 < π x) ∧
      ∀ x : V, π x * expReturnTime P x = 1 := by
  sorry

end MarkovMixing
