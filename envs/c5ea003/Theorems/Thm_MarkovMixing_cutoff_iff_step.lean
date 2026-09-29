-- Prove2me | Theorems.Thm_MarkovMixing_cutoff_iff_step
-- name    : MarkovMixing.cutoff_iff_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:19.308948+00:00
-- url     : https://prove2.me/theorems/10420fa7-8cd5-4937-8211-f57e9d4d5942
-- title:
--   Cutoff is a step-function profile
-- statement:
--   Consider a **family of chains**: for each $n$, an irreducible and aperiodic chain $P^{(n)}$ on a finite state space with stationary distribution $\pi_n$ — irreducible and aperiodic so that it does converge to $\pi_n$ and its mixing times are genuine finite times. Write $d_n(t)=\max_x\|P^{(n)t}(x,\cdot)-\pi_n\|_{TV}$ for the worst-case total variation distance to stationarity ($\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$), $t^{(n)}_{\mathrm{mix}}(\varepsilon)=\min\{t:d_n(t)\le\varepsilon\}$, and $t^{(n)}_{\mathrm{mix}}=t^{(n)}_{\mathrm{mix}}(1/4)$. The family has a **cutoff** when $t^{(n)}_{\mathrm{mix}}(\varepsilon)/t^{(n)}_{\mathrm{mix}}(1-\varepsilon)\to1$ for every $0<\varepsilon<1$: the times to mix well and to mix barely agree to leading order.
--
--   The theorem (Lemma 18.1 of Levin–Peres–Wilmer) asserts that cutoff is equivalent to the distance profile converging to a step function on the $t_{\mathrm{mix}}$ time scale: the family has a cutoff **if and only if** for every $c>0$
--
--   1. $c<1$ implies $d_n\bigl(\lfloor c\,t^{(n)}_{\mathrm{mix}}\rfloor\bigr)\to1$ — just before the mixing time the family is asymptotically unmixed;
--   2. $c>1$ implies $d_n\bigl(\lfloor c\,t^{(n)}_{\mathrm{mix}}\rfloor\bigr)\to0$ — just after it, asymptotically mixed.
--
--   This equivalence is the working definition of cutoff in practice: sharp upper and lower bounds on $d_n$ at times $c\,t_{\mathrm{mix}}$ (as produced for the hypercube in this mission) are exactly what the right-hand side asks for.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 18.1, Lemma 18.1, p. 247

import Definitions.Def_mm_cutoff

namespace MarkovMixing

/-- **Lemma 18.1** (LPW): a sequence of chains has a cutoff if and only if,
on the time scale of `t_mix`, the distance to stationarity approaches a step
function: `d_n(⌊c t_mix⌋) → 1` for `c < 1` and `→ 0` for `c > 1`.

Each chain in the sequence is hypothesized irreducible and aperiodic. LPW
speak of "the mixing time for the `n`-th chain", taking for granted that
`t_mix` is a genuine finite time, which is to say that `d_n(t) → 0`;
`mixingTime` is an infimum over the naturals, and for a chain that never comes
within `ε` of stationarity that infimum is over an empty set and reports the
junk value `0`. -/
theorem cutoff_iff_step {V : ℕ → Type*} [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] [∀ n, Nonempty (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ)
    (hP : ∀ n, IsStochastic (P n)) (hirr : ∀ n, Irreducible (P n))
    (hap : ∀ n, Aperiodic (P n)) (hπ : ∀ n, IsStationary (P n) (π n)) :
    HasCutoff P π ↔
      ∀ c : ℝ, 0 < c →
        (c < 1 → Filter.Tendsto
          (fun n => distStationary (P n) (π n) ⌊c * tMix (P n) (π n)⌋₊)
          Filter.atTop (nhds 1)) ∧
        (1 < c → Filter.Tendsto
          (fun n => distStationary (P n) (π n) ⌊c * tMix (P n) (π n)⌋₊)
          Filter.atTop (nhds 0)) := by
  sorry

end MarkovMixing
