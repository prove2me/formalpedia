-- Prove2me | Theorems.Thm_MarkovMixing_colorings_mixing
-- name    : MarkovMixing.colorings_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:09:45.296907+00:00
-- url     : https://prove2.me/theorems/d48caf49-753c-4c3b-b972-bf1d6ce58e03
-- title:
--   Theorem 5.7 -- fast mixing of the Metropolis chain on colorings
-- statement:
--   Let $G$ be a graph on $n$ vertices with maximal degree $\Delta$, and fix a number of colors $q$. A $q$-coloring of the vertices is **proper** if adjacent vertices always receive distinct colors. The **Metropolis chain on proper colorings** moves as follows: pick a vertex $v$ and a color $k$ uniformly at random, recolor $v$ with $k$ if the result is again a proper coloring, and do nothing otherwise. Its stationary distribution is uniform on the proper colorings. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 5.7 of Levin–Peres–Wilmer) asserts: if $q>3\Delta$ — enough colors relative to the degree — then for every $0<\varepsilon\le1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\Bigl(1-\frac{3\Delta}{q}\Bigr)^{-1} n\,\bigl(\log n+\log\varepsilon^{-1}\bigr)\;+\;1.$$
--   So with $q>3\Delta$ colors the chain mixes in order $n\log n$ steps. (The trailing $+1$ absorbs the rounding of the real-valued bound to an integer time.)
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 5.4.1, Theorem 5.7, p. 70

import Definitions.Def_mm_coupling
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 5.7** (LPW): for the Metropolis chain on proper `q`-colorings
of a graph with `n` vertices and maximal degree `Δ`, if `q > 3Δ`, then with
`c_met(Δ,q) = 1 − 3Δ/q`,
`t_mix(ε) ≤ c_met(Δ,q)⁻¹ n (log n + log(1/ε)) + 1`. -/
theorem colorings_mixing {Vv : Type*} [Fintype Vv] [DecidableEq Vv] [Nonempty Vv]
    (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ)
    (hq : 3 * G.maxDegree < q) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (mixingTime (coloringMetropolis G q)
        (uniformDist {c : Vv → Fin q // IsProperColoring G c}) ε : ℝ) ≤
      (1 - 3 * (G.maxDegree : ℝ) / q)⁻¹ * (Fintype.card Vv) *
        (Real.log (Fintype.card Vv) + Real.log ε⁻¹) + 1 := by
  sorry

end MarkovMixing
