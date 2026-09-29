-- Prove2me | Theorems.Thm_MarkovMixing_torus_mixing
-- name    : MarkovMixing.torus_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:09:31.956083+00:00
-- url     : https://prove2.me/theorems/ec495602-d5fa-475a-89db-c226f391a8ed
-- title:
--   Theorem 5.5 -- the lazy walk on the torus mixes in order $n^2$
-- statement:
--   The **$d$-dimensional discrete torus** $\mathbb Z_n^d$ is the graph whose vertices are the $d$-tuples of residues mod $n$, two vertices being adjacent when they agree in all coordinates but one and differ by $\pm1\pmod n$ there. The **lazy random walk** on it stays put with probability $\tfrac12$ and otherwise moves to a uniformly chosen neighbour; its stationary distribution is uniform. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first time $t$ at which $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Theorem 5.5 of Levin–Peres–Wilmer) asserts: for every dimension $d\ge1$ there is a constant $c=c(d)>0$, depending only on $d$, such that for every side length $n\ge2$ and every tolerance $0<\varepsilon\le\tfrac12$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;c\,n^2\,\log_2\varepsilon^{-1}.$$
--   The walk on the torus mixes in order $n^2$ steps, uniformly in the side length — proved in the book by a coordinatewise coupling.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 5.3.2, Theorem 5.5, pp. 65-66

import Definitions.Def_mm_coupling
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MarkovMixing

/-- **Theorem 5.5** (LPW): the lazy random walk on the `d`-dimensional torus
`ℤ_n^d` satisfies `t_mix(ε) ≤ c(d) n² log₂(ε⁻¹)` for a constant `c(d)`
depending only on the dimension `d`. -/
theorem torus_mixing (d : ℕ) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (mixingTime (lazy (graphWalk (torusGraph d n)))
          (uniformDist (Fin d → ZMod n)) ε : ℝ) ≤
        c * n ^ 2 * Real.logb 2 ε⁻¹ := by
  sorry

end MarkovMixing
