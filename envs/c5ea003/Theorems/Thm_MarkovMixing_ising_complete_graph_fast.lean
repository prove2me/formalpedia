-- Prove2me | Theorems.Thm_MarkovMixing_ising_complete_graph_fast
-- name    : MarkovMixing.ising_complete_graph_fast
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:38.299112+00:00
-- url     : https://prove2.me/theorems/93fc9447-8d1a-41f6-8bce-d3ea05a77d77
-- title:
--   Curie--Weiss: fast mixing for $\alpha<1$
-- statement:
--   The **Curie–Weiss model** is the Ising model on the complete graph $K_n$: spins $\pm1$ on $n$ vertices, every pair interacting, with Gibbs distribution $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}}\sigma(v)\sigma(w)\bigr)$ at inverse temperature $\beta=\alpha/n$ — the $1/n$ scaling that makes the total interaction per site of constant order, with $\alpha$ the effective temperature parameter. The **Glauber dynamics** re-samples a uniformly chosen site from the conditional distribution; the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_\sigma\|P^t(\sigma,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 15.3(i) of Levin–Peres–Wilmer) asserts: for every $n\ge2$, every $0<\alpha<1$, and every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;\Bigl\lceil\frac{n\,\bigl(\log n+\log(1/\varepsilon)\bigr)}{1-\alpha}\Bigr\rceil.$$
--
--   Below the critical value $\alpha=1$ the mean-field dynamics mixes in order $n\log n$ steps. The proof is one line from the high-temperature theorem of this mission: on $K_n$ the degree is $n-1$ and $(n-1)\tanh(\alpha/n)\le\alpha$. The companion theorem shows that above $\alpha=1$ the same dynamics needs exponentially many steps — the dynamical phase transition.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.2, Theorem 15.3(i), Eq. (15.8), p. 203

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 15.3(i)** (LPW): for the Glauber dynamics of the Ising model
on the complete graph on `n` vertices at `β = α/n` with `α < 1`,
`t_mix(ε) ≤ ⌈n(log n + log(1/ε))/(1−α)⌉` (the ceiling absorbs integer
rounding). -/
theorem ising_complete_graph_fast (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα : α < 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
        (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) ε : ℝ) ≤
      ⌈(n : ℝ) * (Real.log n + Real.log (1 / ε)) / (1 - α)⌉₊ := by
  sorry

end MarkovMixing
