-- Prove2me | Theorems.Thm_minsky_papert_symmetrization
-- name    : minsky_papert_symmetrization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-08T21:25:51.473688+00:00
-- url     : https://prove2.me/theorems/300dadce-681e-4d4a-b916-6daa13841a59
-- statement:
--   **Minsky–Papert symmetrization.**
--
--   For every multivariate real polynomial $p \in \mathbb{R}[X_1, \ldots, X_b]$ of total degree $d$, there exists a univariate polynomial $Q \in \mathbb{R}[X]$ of degree $\le d$ such that for every integer $t \in \{0, 1, \ldots, b\}$,
--   $$Q(t) \cdot \binom{b}{t} \;=\; \sum_{\substack{y \in \{0,1\}^b \\ |y| = t}} p(y),$$
--   where $|y|$ is the Hamming weight and $p(y)$ denotes evaluation at the $0/1$-vector $y$.
--
--   The multiplicative formulation avoids division by zero in the (vacuous) range $t > b$, where $\binom{b}{t} = 0$ and the right-hand side is also empty; for $t \le b$ the binomial coefficient is positive and so $Q(t)$ is uniquely determined by the slice average.
--
--   Proof idea: average $p$ over the symmetric group $S_b$ acting on coordinates to get a *symmetric* polynomial $\tilde p$ of total degree $\le d$. On any Boolean input, $\tilde p$ depends only on the Hamming weight, and the $b+1$ slice values are interpolated by a univariate polynomial of degree $\le d$ — explicitly, the value at integer $t$ comes from the $\le d$-th elementary-symmetric expansion of $\tilde p$.
--
--   Standard tool of the polynomial method (Minsky–Papert 1969 §1.5; Nisan–Szegedy 1994).
-- source:
--   Minsky, Marvin L., and Seymour A. Papert. "Perceptrons: an introduction to computational geometry." MIT Press (1969). The polynomial-degree-preserving symmetrization is established in §1.5; widely reused in the polynomial method, including Nisan and Szegedy (1994).

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Minsky–Papert symmetrization

For any multivariate real polynomial `p : ℝ[X_1, …, X_b]` of total degree
`≤ d`, the function obtained by *averaging* `p` over the Hamming-weight-`t`
slice of the Boolean cube `{0,1}^b` extends to a univariate polynomial of
degree `≤ d`. This is the crucial dimensionality-reduction step in the
Nisan–Szegedy proof of `bs(f) ≤ 2 · deg(f)²`.

Stated multiplicatively (`Q(t) · (b choose t) = sum`) to avoid the division-by-
zero pathology when `t > b` (`b.choose t = 0`); for `t ≤ b`, `b.choose t > 0`
and so `Q(t)` is determined by the sum.

Left as a platform leaf — DEFERRED. Will be tackled in a separate session.
-/

open MvPolynomial

/-- **Minsky–Papert (1969) symmetrization.** For any multivariate polynomial
`p : ℝ[X_1, …, X_b]`, there exists a univariate polynomial `Q` of natDegree
`≤ p.totalDegree` such that for every integer `t ∈ {0, 1, …, b}`,
`Q(t) · (b choose t)` equals the sum of `p` evaluated at all weight-`t`
0/1-vectors. -/

theorem minsky_papert_symmetrization
    {b : ℕ} (p : MvPolynomial (Fin b) ℝ) :
    ∃ Q : Polynomial ℝ,
      Q.natDegree ≤ p.totalDegree ∧
      ∀ t : ℕ, t ≤ b →
        Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) =
          ∑ y ∈ (Finset.univ : Finset (Fin b → Bool)).filter
                  (fun y => ((Finset.univ : Finset (Fin b)).filter
                                (fun i => y i = true)).card = t),
            MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p := by sorry
