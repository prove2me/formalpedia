-- Prove2me | Theorems.Thm_MarkovMixing_glauber_colorings_mixing
-- name    : MarkovMixing.glauber_colorings_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:25:30.263972+00:00
-- url     : https://prove2.me/theorems/4cb6eeda-f27f-469b-8db7-21bb7a9677e2
-- title:
--   Glauber dynamics on proper colorings mixes in $O(n\log n)$ for $q>2\Delta$
-- statement:
--   Let $G$ be a graph on $n$ vertices with maximum degree $\Delta$, and fix a number of colors $q$. A $q$-coloring of the vertices is **proper** when adjacent vertices receive distinct colors, and the **Glauber dynamics on proper colorings** picks a uniform vertex and re-samples its color from the uniform distribution on the colorings that agree with the current one elsewhere — that is, uniformly among the colors legal at that vertex. Its stationary distribution is uniform over proper colorings. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Theorem 14.8 of Levin–Peres–Wilmer, the capstone of Chapter 14) asserts: if $q>2\Delta$, then for every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\Bigl\lceil\frac{q-\Delta}{q-2\Delta}\;n\,\bigl(\log n-\log\varepsilon\bigr)\Bigr\rceil.$$
--   With a bit more than twice as many colors as the maximum degree, the dynamics mixes in order $n\log n$ steps. This is the flagship application of path coupling: colorings differing at one vertex are coupled by matching their proposed recolorings, and the single-edge contraction rate $(q-2\Delta)/\bigl(n(q-\Delta)\bigr)$ falls out of counting the disagreeing proposals.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 14.3, Theorem 14.8, Eq. (14.17), p. 193

import Definitions.Def_mm_transport
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 14.8** (LPW), the capstone of Chapter 14: for the Glauber
dynamics on proper `q`-colorings of a graph with `n` vertices and maximum
degree `Δ`, if `q > 2Δ`, then
`t_mix(ε) ≤ ⌈((q−Δ)/(q−2Δ)) n (log n − log ε)⌉`. -/
theorem glauber_colorings_mixing {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj] (q : ℕ)
    (hq : 2 * G.maxDegree < q) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime (coloringGlauber G q)
        (uniformDist {c : Vv → Fin q // IsProperColoring G c}) ε : ℝ) ≤
      ⌈((q : ℝ) - G.maxDegree) / ((q : ℝ) - 2 * G.maxDegree) *
        (Fintype.card Vv) *
        (Real.log (Fintype.card Vv) - Real.log ε)⌉₊ := by
  sorry

end MarkovMixing
