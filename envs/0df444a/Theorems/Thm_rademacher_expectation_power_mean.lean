-- Prove2me | Theorems.Thm_rademacher_expectation_power_mean
-- name    : rademacher_expectation_power_mean
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T21:29:23.556034+00:00
-- url     : https://prove2.me/theorems/70ff9358-6e26-492c-aeed-27cfa661c82b
-- statement:
--   **Power-mean (Jensen) inequality for the uniform Rademacher sign average.** The map $\texttt{rademacherExpectation}$ is the expectation under the uniform probability measure on the discrete cube of $\pm1$ sign assignments (each of the $2^N$ assignments has weight $2^{-N}$, and these weights sum to $1$).  For any nonnegative integrand $F\ge0$ and exponents $0 < r \le s$, the $r$-th moment is dominated by the $s$-th moment raised to the power $r/s$:
--
--   $$\mathbb{E}_{\varepsilon}\big[F(\varepsilon)^{\,r}\big]\;\le\;\Big(\mathbb{E}_{\varepsilon}\big[F(\varepsilon)^{\,s}\big]\Big)^{r/s}.$$
--
--   Equivalently $\|F\|_{L^r} \le \|F\|_{L^s}$ for $r\le s$ on a probability space (nesting of $L^p$ norms / power-mean monotonicity), a consequence of Jensen's inequality applied to the convex map $t \mapsto t^{s/r}$.  This is the analytic step that lets one pass from an even-integer moment $s = 2n$ down to a real moment $r = q \le 2n$ in the noncommutative Khintchine assembly.
-- source:
--   Power-mean / nesting of L^p norms on a probability space (Jensen's inequality). Used in CR2009 (arXiv:0805.4471) section 6.1 to pass from the even-integer Buchholz moment to a general real moment q >= 2.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped BigOperators

theorem rademacher_expectation_power_mean
    {n1 n2 : Nat} (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (F : Finset (Fin n1 × Fin n2) → ℝ) (hF : ∀ eps, 0 ≤ F eps) :
    rademacherExpectation (fun eps => (F eps) ^ r)
      ≤ Real.rpow (rademacherExpectation (fun eps => (F eps) ^ s)) (r / s) := by sorry
