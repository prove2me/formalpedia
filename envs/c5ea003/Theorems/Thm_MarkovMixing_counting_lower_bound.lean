-- Prove2me | Theorems.Thm_MarkovMixing_counting_lower_bound
-- name    : MarkovMixing.counting_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:24:25.317208+00:00
-- url     : https://prove2.me/theorems/76310f40-7520-4cd7-b8a6-e2b57cfd5007
-- title:
--   Section 7.1.1 -- the counting bound
-- statement:
--   Let $P$ be an irreducible, aperiodic Markov chain on a finite state space $V$ whose stationary distribution is **uniform**. Let
--   $$\Delta=\max_{x\in V}\#\{y: P(x,y)>0\}$$
--   be the maximal number of states reachable from a single state in one step. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (the counting bound, §7.1.1, display (7.2) of Levin–Peres–Wilmer) asserts: for every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\ge\;\frac{\log\bigl(|V|\,(1-\varepsilon)\bigr)}{\log\Delta}.$$
--   The reason: in $t$ steps the chain can reach at most $\Delta^t$ states, and until $\Delta^t$ is comparable to $|V|$ the time-$t$ distribution misses most of a uniform target. In particular chains with bounded branching need at least $\log|V|/\log\Delta$ steps to mix.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.1.1, Eq. (7.2), p. 87

import Definitions.Def_mm_lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **§7.1.1, Eq. (7.2)** (LPW), the counting bound: for a chain with uniform
stationary distribution, `t_mix(ε) ≥ log(|Ω|(1−ε)) / log Δ`, where `Δ` is
the maximal number of states accessible in one step. -/
theorem counting_lower_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (hπ : IsStationary P (uniformDist V))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log ((Fintype.card V : ℝ) * (1 - ε)) / Real.log (maxOutDegree P) ≤
      (mixingTime P (uniformDist V) ε : ℝ) := by
  sorry

end MarkovMixing
