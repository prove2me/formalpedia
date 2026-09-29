-- Prove2me | Theorems.Thm_MarkovMixing_ising_cycle
-- name    : MarkovMixing.ising_cycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:24.69658+00:00
-- url     : https://prove2.me/theorems/f5096b19-0ec0-40a1-bb8f-4bb25031d47d
-- title:
--   Ising on the cycle: $n\log n$ mixing at every temperature
-- statement:
--   The **Ising model on the $n$-cycle** puts spins $\pm1$ on $\mathbb Z_n$ (each residue adjacent to its two neighbours) with Gibbs distribution $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}\in E}\sigma(v)\sigma(w)\bigr)$ at inverse temperature $\beta>0$, and its **Glauber dynamics** re-samples a uniformly chosen site from the conditional distribution. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_\sigma\|P^t(\sigma,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$. Set
--   $$c_O(\beta)=1-\tanh(2\beta),$$
--   which is positive for every $\beta$.
--
--   The theorem (Theorem 15.4 of Levin–Peres–Wilmer) asserts: for any fixed $0<\varepsilon<1$ and any margin $\delta>0$ there is an $N$ such that for all $n\ge N$,
--   $$\frac{(1-\delta)\,n\log n}{2\,c_O(\beta)}\;\le\;t_{\mathrm{mix}}(\varepsilon)\;\le\;\frac{(1+\delta)\,n\log n}{c_O(\beta)}.$$
--
--   On the cycle the dynamics mixes in $n\log n$ steps at **every** temperature — no phase transition in one dimension, in sharp contrast to the complete graph of the companion theorems. The upper bound is the even-degree case of the high-temperature theorem (every vertex of the cycle has degree $2$, so the condition $(\Delta/2)\tanh(2\beta)=\tanh(2\beta)<1$ always holds); the lower bound runs Wilson's method (Mission VII) with a Fourier-mode eigenfunction.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.3, Theorem 15.4, Eq. (15.10), p. 204

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 15.4** (LPW): for the Glauber dynamics of the Ising model on
the `n`-cycle at any `β > 0`, with `c_O(β) = 1 − tanh(2β)`, the mixing time
is `n log n` up to constants:
`(1+o(1)) n log n/(2c_O) ≤ t_mix(ε) ≤ (1+o(1)) n log n/c_O`. -/
theorem ising_cycle (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ inst : NeZero n,
      (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) ≤
        (1 + δ) * n * Real.log n / (1 - Real.tanh (2 * β)) ∧
      (1 - δ) * n * Real.log n / (2 * (1 - Real.tanh (2 * β))) ≤
        (mixingTime (glauber (isingDist (cycleGraph n) β))
          (isingDist (cycleGraph n) β) ε : ℝ) := by
  sorry

end MarkovMixing
