-- Prove2me | Theorems.Thm_MarkovMixing_time_reversal
-- name    : MarkovMixing.time_reversal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:57.753483+00:00
-- url     : https://prove2.me/theorems/41095e0e-a114-4fd0-948e-81183de04384
-- title:
--   Proposition 1.22 -- the time reversal of a chain
-- statement:
--   For an irreducible chain with stationary distribution $\pi$, the time reversal $\hat P(x,y)=\pi(y)P(y,x)/\pi(x)$ is a stochastic matrix, $\pi$ is stationary for $\hat P$, and started from $\pi$ the reversed chain traverses every trajectory with the same probability as the original chain traverses the reversed trajectory: $$\pi(x_0)P(x_0,x_1)\cdots P(x_{t-1},x_t)=\pi(x_t)\hat P(x_t,x_{t-1})\cdots\hat P(x_1,x_0).$$
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.6, Proposition 1.22, p. 15

import Definitions.Def_mm_path

namespace MarkovMixing

/-- **Proposition 1.22** (LPW): for an irreducible chain with stationary
distribution `π`, the time reversal `P̂` is a stochastic matrix, `π` is
stationary for `P̂`, and started from `π` the chain run through `P̂` traverses
every trajectory with the same probability as the original chain traverses the
reversed trajectory. -/
theorem time_reversal {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) :
    IsStochastic (timeReversal P π) ∧ IsStationary (timeReversal P π) π ∧
    ∀ (t : ℕ) (ω : Fin (t + 1) → V),
      π (ω 0) * pathWeight P ω =
        π (ω (Fin.last t)) * pathWeight (timeReversal P π) (fun i => ω i.rev) := by
  sorry

end MarkovMixing
