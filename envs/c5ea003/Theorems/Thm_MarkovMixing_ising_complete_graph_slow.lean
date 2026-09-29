-- Prove2me | Theorems.Thm_MarkovMixing_ising_complete_graph_slow
-- name    : MarkovMixing.ising_complete_graph_slow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:02.250558+00:00
-- url     : https://prove2.me/theorems/96f653f1-5a53-475e-b4e4-0c73360d94c7
-- title:
--   Curie--Weiss: exponentially slow mixing for $\alpha>1$
-- statement:
--   The **Curie–Weiss model** is the Ising model on the complete graph $K_n$: spins $\pm1$ on $n$ vertices with Gibbs distribution $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}}\sigma(v)\sigma(w)\bigr)$ at $\beta=\alpha/n$, and the **Glauber dynamics** re-samples a uniformly chosen site from the conditional distribution. The **mixing time** $t_{\mathrm{mix}}$ is the first $t$ at which $\max_\sigma\|P^t(\sigma,\cdot)-\pi\|_{TV}\le\tfrac14$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ the total variation distance.
--
--   The theorem (Theorem 15.3(ii) of Levin–Peres–Wilmer) asserts: for every $\alpha>1$ there are a rate $r>0$ and a constant $C>0$ such that for all sufficiently large $n$,
--   $$t_{\mathrm{mix}}\;\ge\;C\,e^{\,r\,n}.$$
--
--   Above the critical temperature parameter the dynamics is **exponentially slow** — the low-temperature half of the dynamical phase transition, in the sharpest possible contrast with the $n\log n$ mixing below $\alpha=1$. The obstruction is an energy barrier: at $\alpha>1$ the magnetization $\sum_v\sigma(v)$ concentrates near two symmetric values $\pm m^*n$, and passing from one well to the other forces the chain through configurations of exponentially small stationary mass; the bottleneck bound of Mission IV converts that barrier into the exponential lower bound.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.2, Theorem 15.3(ii), pp. 203-204

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 15.3(ii)** (LPW): for the Glauber dynamics of the Ising model
on the complete graph at `β = α/n` with `α > 1`, the mixing time is
exponentially large: there are `r(α) > 0` and `C > 0` with
`t_mix ≥ C e^{r(α) n}` for all large `n`. -/
theorem ising_complete_graph_slow (α : ℝ) (hα : 1 < α) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * Real.exp (r * n) ≤
        (tMix (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
          (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) : ℝ) := by
  sorry

end MarkovMixing
