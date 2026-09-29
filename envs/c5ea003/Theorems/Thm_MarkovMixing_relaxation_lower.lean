-- Prove2me | Theorems.Thm_MarkovMixing_relaxation_lower
-- name    : MarkovMixing.relaxation_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:46:14.468315+00:00
-- url     : https://prove2.me/theorems/ddc227d6-3594-4d83-a9f5-e553e6b7f8a3
-- title:
--   Theorem 12.4 -- mixing is at least the relaxation time
-- statement:
--   Let $P$ be an irreducible, aperiodic Markov chain on a finite state space $V$, reversible with respect to its stationary distribution $\pi$ (detailed balance: $\pi(x)P(x,y)=\pi(y)P(y,x)$). Among the eigenvalues of $P$ — the real $\lambda$ admitting a nonzero $f$ with $Pf=\lambda f$ — let $\lambda_\star$ be the largest absolute value of an eigenvalue different from $1$; the **absolute spectral gap** is $\gamma_\star=1-\lambda_\star$ and the **relaxation time** is $t_{\mathrm{rel}}=1/\gamma_\star$. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\pi\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$.
--
--   The theorem (Theorem 12.4 of Levin–Peres–Wilmer) asserts: for every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\ge\;\bigl(t_{\mathrm{rel}}-1\bigr)\,\log\!\Bigl(\frac{1}{2\varepsilon}\Bigr).$$
--   A chain cannot mix faster than it relaxes: an eigenfunction with eigenvalue close to $1$ decays like $\lambda_\star^t$ and remains a visible witness against stationarity for about $t_{\mathrm{rel}}$ steps. Together with the companion upper bound $t_{\mathrm{mix}}(\varepsilon)\le\log(1/\varepsilon\pi_{\min})\,t_{\mathrm{rel}}+1$, this sandwiches the mixing time between $t_{\mathrm{rel}}$ and $t_{\mathrm{rel}}\log(1/\pi_{\min})$ for reversible chains.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 12.2, Theorem 12.4, Eq. (12.12), p. 155

import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 12.4** (LPW): for a reversible, irreducible, aperiodic chain,
`t_mix(ε) ≥ (t_rel − 1) log(1/(2ε))`. -/
theorem relaxation_lower {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (relaxationTime P - 1) * Real.log (1 / (2 * ε)) ≤
      (mixingTime P π ε : ℝ) := by
  sorry

end MarkovMixing
