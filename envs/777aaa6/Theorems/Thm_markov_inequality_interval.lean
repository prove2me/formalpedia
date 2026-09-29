-- Prove2me | Theorems.Thm_markov_inequality_interval
-- name    : markov_inequality_interval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-09T02:35:49.140472+00:00
-- url     : https://prove2.me/theorems/25ca171e-f5b7-4bc1-993c-40f4c0382b80
-- statement:
--   **Markov's brothers inequality on an interval (A. A. Markov, 1889).**
--
--   For every univariate real polynomial $Q$ of degree $\le d$ absolutely bounded by $M$ on a closed interval $[a, b]$ (with $a < b$), the derivative is uniformly bounded:
--   $$|Q'(c)| \;\le\; \frac{2 \, d^2 \, M}{b - a} \qquad \text{for every } c \in [a, b].$$
--
--   The constant $2 d^2 / (b - a)$ is sharp, achieved at the endpoints by the appropriately scaled Chebyshev polynomial $T_d\!\left( (2x - a - b)/(b - a) \right)$.
--
--   This is one of the foundational classical results of polynomial inequalities. *Not currently in Mathlib at the inside-the-interval level* — Mathlib has the outside-the-interval extremal property (`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` for $x \ge 1$), but the inside-the-interval Markov bound requires a separate argument via the Chebyshev expansion + sign analysis. Estimated 300-500 Lean lines.
-- source:
--   A. A. Markov. "On a question by D. I. Mendeleev." Zapiski Petersburg Akad. Nauk 62 (1889): 1-24. Classical Markov's brothers inequality on an interval. Constant 2 d² M / (b - a) is sharp, achieved by Chebyshev.

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

/-!
# Markov's brothers inequality on a continuous interval

Classical inequality (A. A. Markov, 1889): for univariate real polynomial
`Q` of degree `≤ d` absolutely bounded by `M` on a closed interval
`[a, b]` with `a < b`, the derivative is uniformly bounded by `2 d² M /
(b - a)` on the same interval. The constant `2 d² / (b - a)` is sharp,
achieved by the appropriately scaled Chebyshev polynomial `T_d`.

This is one of the foundational classical results in the theory of
polynomial inequalities, but is *not* present in Mathlib at the
inside-the-interval level (Mathlib has the outside-the-interval extremal
property `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
for `x ≥ 1`, but the inside-the-interval Markov bound requires a separate
argument via Chebyshev expansion + sign analysis).

Left as a platform leaf — DEFERRED. Sub-leaf of `markov_polya_grid`.
Estimated 300-500 lines.
-/

/-- **Markov's brothers inequality on `[a, b]`.**

For real polynomial `Q` of degree `≤ d` with `|Q(x)| ≤ M` for every
`x ∈ [a, b]` (with `a < b`), the derivative satisfies the sharp bound
`|Q'(c)| ≤ 2 d² M / (b - a)` for every `c ∈ [a, b]`. -/

theorem markov_inequality_interval
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (M : ℝ)
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ x : ℝ, a ≤ x → x ≤ b → |Q.eval x| ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 * M / (b - a) := by sorry
