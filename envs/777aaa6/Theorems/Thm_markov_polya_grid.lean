-- Prove2me | Theorems.Thm_markov_polya_grid
-- name    : markov_polya_grid
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-05-09T02:29:37.206975+00:00
-- url     : https://prove2.me/theorems/ae49ce1f-28c2-41b8-add9-dcfee332af04
-- statement:
--   **Markov-Pólya inequality on the integer grid (small-degree regime).**
--
--   For every univariate real polynomial $Q \in \mathbb{R}[X]$ of degree $\le d$ that is absolutely bounded by $1$ on the integer grid $\{0, 1, \ldots, b\}$ (with $b \ge 1$), and assuming the regime hypothesis $2 d^2 \le b$, the derivative satisfies the sharp continuous Markov-style bound
--   $$|Q'(c)| \;\le\; \frac{2 \, d^2}{b} \qquad \text{for every } c \in [0, b].$$
--
--   The regime hypothesis $2 d^2 \le b$ is essential: when $d$ is large compared to $\sqrt{b/2}$, Lagrange interpolation through the integer points can exhibit the standard Lebesgue-constant blow-up, and the integer-grid bound need not propagate to the continuous interval. In the small-degree regime $2 d^2 \le b$, however, the polynomial is "smooth" in a precise sense — the Coppersmith-Rivlin / Ehlich-Zeller continuous-extension constant approaches $1$ — and the classical Markov-on-an-interval inequality applies with the sharp constant $2 d^2 / b$.
--
--   This is the *missing analytic ingredient* in Nisan and Szegedy's proof of $\mathrm{bs}(f) \le 2 \deg(f)^2$ (corresponding to the small-degree case of NS 1994 Lemma 2). The complementary large-degree case ($2 d^2 > b$) is trivial since $b \le 2 d^2$ holds automatically there.
--
--   Likely proof strategy (NOT formalised here): (i) a Coppersmith-Rivlin-type lemma showing that the integer-grid bound propagates to a continuous bound on $[0, b]$ in the small-degree regime, (ii) the classical Markov inequality on an interval. Mathlib's `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` is a relevant building block. Estimated 600-1000 Lean lines, may need its own decomposition.
-- source:
--   Markov, A. A. (1889) — original sharp Markov inequality on intervals; Pólya, George. "Sur l'approximation d'une fonction continue par des polynômes de degré donné." Compt. Rend. Acad. Sci. (1928) — extension to integer-grid bounded polynomials in the small-degree regime; Coppersmith, Don, and Theodore J. Rivlin. "The growth of polynomials bounded at equally spaced points." SIAM J. Math. Anal. 23.4 (1992): 970-983 — refined continuous-extension constants. Used in Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313.

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

/-!
# Markov-Pólya inequality on the integer grid

For a univariate real polynomial `Q` of degree `≤ d` with `|Q(j)| ≤ 1` on
the integer grid `{0, 1, …, b}`, in the regime `2·d² ≤ b` (i.e. `d` is
small relative to `b`), the derivative satisfies the sharp continuous
Markov-style bound `|Q'(x)| ≤ 2 d² / b` everywhere on `[0, b]`.

The regime hypothesis `2·d² ≤ b` is essential: when `d` is large (`d² > b`),
Lagrange interpolation through the integer points can blow up exponentially,
so the integer-grid bound does not propagate to the continuous interval
without restriction. In the small-`d` regime, the polynomial is "smooth"
in a precise sense (Coppersmith-Rivlin / Ehlich-Zeller continuous extension
constant approaches `1`), and the standard Markov-on-an-interval inequality
applies with the sharp constant `2 d² / b`.

This is the *missing analytic ingredient* in the Nisan-Szegedy proof of
`bs(f) ≤ 2 deg(f)²` (corresponds to NS 1994 Lemma 2 in the small-degree
regime; the large-degree case is trivial since `b ≤ 2 d²` automatically
holds when `2 d² > b`).

Left as a platform leaf — DEFERRED. Estimated 600-1000 lines, may require
formalising the Coppersmith-Rivlin extension lemma + classical Markov on
intervals as additional sub-leaves. The Mathlib-internal extremal-Chebyshev
results (`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`)
provide a starting point for the endpoint Markov bound.
-/

/-- **Markov-Pólya inequality, integer-grid form (small-degree regime).**

For univariate real polynomial `Q` with `Q.natDegree ≤ d`, absolute value
bounded by `1` on `{0, 1, …, b}` (with `b ≥ 1`), and `2 d² ≤ b`, the
derivative is uniformly bounded by `2 d² / b` on the continuous interval
`[0, b]`. -/

theorem markov_polya_grid
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1)
    (h_regime : 2 * d^2 ≤ b) :
    ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 / (b : ℝ) := by sorry
