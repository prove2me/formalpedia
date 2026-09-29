-- Prove2me | Theorems.Thm_MarkovMixing_ising_high_temperature
-- name    : MarkovMixing.ising_high_temperature
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:57.095957+00:00
-- url     : https://prove2.me/theorems/47bcc85c-0217-4d04-b28b-658b1f3a583f
-- title:
--   High-temperature fast mixing of Glauber dynamics
-- statement:
--   Let $G$ be a graph on $n$ vertices with maximum degree $\Delta$. The **Ising model** at inverse temperature $\beta>0$ puts spins $\pm1$ on the vertices with Gibbs distribution $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}\in E}\sigma(v)\sigma(w)\bigr)$, and its **Glauber dynamics** picks a uniform vertex and re-samples its spin from $\pi$ conditioned on the other spins. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_\sigma\|P^t(\sigma,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Theorem 15.1 of Levin–Peres–Wilmer, the capstone of Chapter 15) asserts, for every $0<\varepsilon<1$:
--
--   1. if $\Delta\tanh\beta<1$, then $\displaystyle t_{\mathrm{mix}}(\varepsilon)\le\Bigl\lceil\frac{n\bigl(\log n+\log(1/\varepsilon)\bigr)}{1-\Delta\tanh\beta}\Bigr\rceil$;
--   2. if every vertex of $G$ has even degree and $(\Delta/2)\tanh(2\beta)<1$, the same bound holds with $1-(\Delta/2)\tanh(2\beta)$ in the denominator — a strictly weaker temperature condition.
--
--   At high temperature the Glauber dynamics mixes in order $n\log n$ steps on **any** graph — the fundamental fast-mixing criterion for spin systems. The proof is path coupling (Mission VIII) with the one-site coupling whose disagreement probability the tanh lemma controls; since $\tanh\beta<\beta$, condition 1 holds in particular whenever $\beta<1/\Delta$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.1, Theorem 15.1, Eqs. (15.1)-(15.2), pp. 201-202

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 15.1** (LPW), the capstone of Chapter 15: fast mixing of the
Ising Glauber dynamics at high temperature.  On a graph with `n` vertices
and maximal degree `Δ`:
(i) if `Δ tanh β < 1`, then with `c(β) = 1 − Δ tanh β`,
`t_mix(ε) ≤ ⌈n(log n + log(1/ε))/c(β)⌉`;
(ii) if every vertex has even degree and `(Δ/2) tanh 2β < 1`, then the same
bound holds with `c_e(β) = 1 − (Δ/2) tanh 2β`. -/
theorem ising_high_temperature {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((G.maxDegree : ℝ) * Real.tanh β < 1 →
      (mixingTime (glauber (isingDist G β)) (isingDist G β) ε : ℝ) ≤
        ⌈(Fintype.card Vv : ℝ) *
            (Real.log (Fintype.card Vv) + Real.log (1 / ε)) /
          (1 - (G.maxDegree : ℝ) * Real.tanh β)⌉₊) ∧
    ((∀ v : Vv, Even (G.degree v)) →
      ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β) < 1 →
      (mixingTime (glauber (isingDist G β)) (isingDist G β) ε : ℝ) ≤
        ⌈(Fintype.card Vv : ℝ) *
            (Real.log (Fintype.card Vv) + Real.log (1 / ε)) /
          (1 - ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β))⌉₊) := by
  sorry

end MarkovMixing
