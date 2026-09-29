-- Prove2me | Theorems.Thm_Renewal_renewal_limit
-- name    : Renewal.renewal_limit
-- status  : Proved
-- author  : @ann
-- created : 2026-08-23T18:27:23.885401+00:00
-- url     : https://prove2.me/theorems/3321ac71-186d-4194-8efa-9a44e6a04334
-- title:
--   Erdős–Feller–Pollard renewal theorem: $u_n \to 1/\mu$
-- statement:
--   Let $(f_k)_{k \ge 1}$ be the waiting-time law of a *recurrent event* (a renewal process): $f_k \ge 0$ is the probability that the first occurrence happens at time $k$, and the event is certain to occur, $\sum_{k \ge 1} f_k = 1$. Write
--
--   $$r_n \;=\; \sum_{k > n} f_k \;=\; \Pr\{\tau > n\}$$
--
--   for the tail, so $r_0 = 1$, $r_n = r_{n+1} + f_{n+1}$, and $r_n \to 0$. Let $(u_n)_{n \ge 0}$ be the **renewal sequence**,
--
--   $$u_0 = 1, \qquad u_{n+1} \;=\; \sum_{k=1}^{n+1} f_k\, u_{n+1-k},$$
--
--   so $u_n$ is the probability that the event occurs at time $n$. The mean waiting time is $\mu = \sum_{k \ge 1} k f_k = \sum_{n \ge 0} r_n$, assumed here to be **finite**, and the law is assumed **aperiodic**: no integer $d \ge 2$ divides every $k$ with $f_k > 0$.
--
--   Under these hypotheses the renewal sequence converges to the reciprocal of the mean:
--
--   $$u_n \longrightarrow \frac{1}{\mu} \qquad (n \to \infty).$$
--
--   This is the Erdős–Feller–Pollard theorem, the central limit statement of elementary renewal theory. Aperiodicity is essential: with period $p$ the sequence $u_n$ vanishes off the multiples of $p$ and tends to $p/\mu$ along them. Finiteness of $\mu$ is essential too, though in the opposite direction only: when $\mu = \infty$ one still has $u_n \to 0$, for any period, which is the companion null case.
--
--   **Formalization notes.** The waiting-time law is presented through its tail $r$ rather than through $f$ directly, which is the form in which the hypotheses are usually available and which makes the mean expressible without an infinite sum of the $k f_k$: `hstep` says $r_n - r_{n+1} = f_{n+1}$, `hr0` says $r_0 = 1$, `hrlim` says $r_n \to 0$ (the law is proper), and `hmean` says $\sum_n r_n = \mu$. Aperiodicity appears as `hape`; note that $d \mid 0$ always holds, so the $k$ it produces is automatically nonzero. Only the values $f_1, f_2, \dots$ are used, and $f_0$ is irrelevant. In `hurec` the index is shifted so that the sum runs over `k ∈ Finset.range (n+1)` with summand $f_{k+1} u_{n-k}$, which is $\sum_{j=1}^{n+1} f_j u_{n+1-j}$.
--
--   **Typical use.** For an irreducible aperiodic positive-recurrent Markov chain on a countable state space and a state $x$, taking $r_n = \Pr_x\{\tau_x^+ > n\}$ and $u_n = P^n(x,x)$ satisfies exactly these hypotheses, and the conclusion is the convergence $P^n(x,x) \to 1/\mathbb{E}_x[\tau_x^+] = \pi(x)$.
-- source:
--   P. Erdős, W. Feller and H. Pollard, A property of power series with positive coefficients, Bulletin of the American Mathematical Society 55 (1949), 201-204. See also W. Feller, An Introduction to Probability Theory and Its Applications, Vol. I, 3rd ed., Chapter XIII (Recurrent Events; Renewal Theory), Section 11, Theorem 1.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.NumberTheory.FrobeniusNumber

namespace Renewal

/-- **Erdős–Feller–Pollard renewal theorem** (aperiodic, finite-mean case). -/
theorem renewal_limit (f r u : ℕ → ℝ) (mu : ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hstep : ∀ n : ℕ, r n = r (n + 1) + f (n + 1))
    (hr0 : r 0 = 1)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (hmean : HasSum r mu)
    (hape : ∀ d : ℕ, 2 ≤ d → ∃ k : ℕ, 0 < f k ∧ ¬ (d ∣ k))
    (hu0 : u 0 = 1)
    (hurec : ∀ n : ℕ, u (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k)) :
    Filter.Tendsto u Filter.atTop (nhds (1 / mu)) := by sorry

end Renewal
