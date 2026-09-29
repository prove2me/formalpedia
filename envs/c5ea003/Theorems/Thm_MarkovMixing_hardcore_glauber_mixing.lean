-- Prove2me | Theorems.Thm_MarkovMixing_hardcore_glauber_mixing
-- name    : MarkovMixing.hardcore_glauber_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:09:57.874378+00:00
-- url     : https://prove2.me/theorems/1614670d-0759-43cf-ae65-8460acbb1659
-- title:
--   Theorem 5.8 -- fast mixing of the hardcore Glauber dynamics
-- statement:
--   Let $G$ be a graph on $n$ vertices with maximum degree $\Delta$. A $\{0,1\}$-configuration on the vertices is **hardcore** if no two adjacent vertices are both occupied — the occupied sites form an independent set. The **hardcore model with fugacity** $\lambda>0$ is the distribution on hardcore configurations with $\pi(\sigma)\propto\lambda^{|\sigma|}$, where $|\sigma|$ is the number of occupied sites. The **Glauber dynamics** for $\pi$ picks a uniform vertex and re-samples its occupancy from $\pi$ conditioned on the rest of the configuration; here it is viewed as a chain on the hardcore configurations. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 5.8 of Levin–Peres–Wilmer) asserts: if $\lambda(\Delta-1)<1$, then for every $0<\varepsilon\le1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\frac{n\,(1+\lambda)}{1+\lambda(1-\Delta)}\,\bigl(\log n+\log\varepsilon^{-1}\bigr)\;+\;1.$$
--   Below the threshold $\lambda<(\Delta-1)^{-1}$ the dynamics mixes in order $n\log n$ steps. (The $+1$ absorbs integer rounding.)
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 5.4.2, Theorem 5.8, pp. 70-71

import Definitions.Def_mm_coupling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_mm_mcmc

namespace MarkovMixing

/-- **Theorem 5.8** (LPW): for the Glauber dynamics of the hardcore model
with fugacity `λ` on a graph with `n` vertices and maximum degree `Δ`, if
`λ < (Δ − 1)⁻¹`, then with `c_H(λ) = (1 + λ(1 − Δ))/(1 + λ)`,
`t_mix(ε) ≤ (n / c_H(λ)) (log n + log(1/ε)) + 1`. -/
theorem hardcore_glauber_mixing {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (lam : ℝ) (hlam : 0 < lam) (hc : lam * ((G.maxDegree : ℝ) - 1) < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (mixingTime
        (subChain (glauber (hardcoreDist G lam)) (IsHardcore G))
        (fun σ : {σ : Vv → Bool // IsHardcore G σ} => hardcoreDist G lam σ.1)
        ε : ℝ) ≤
      ((Fintype.card Vv : ℝ) * (1 + lam) / (1 + lam * (1 - (G.maxDegree : ℝ)))) *
        (Real.log (Fintype.card Vv) + Real.log ε⁻¹) + 1 := by
  sorry

end MarkovMixing
