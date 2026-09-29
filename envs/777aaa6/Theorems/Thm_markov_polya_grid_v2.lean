-- Prove2me | Theorems.Thm_markov_polya_grid_v2
-- name    : markov_polya_grid_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-05-09T02:47:54.092111+00:00
-- url     : https://prove2.me/theorems/db2d425b-a2b3-489c-b95a-23de581869c3
-- statement:
--   **Markov-Pólya inequality on the integer grid (Nisan-Szegedy bundled form).**
--
--   For every univariate real polynomial $Q \in \mathbb{R}[X]$ of degree $\le d$ that satisfies
--   $$Q(0) = 0, \qquad |Q(j)| \le 1 \text{ for every integer } j \in \{0, 1, \ldots, b\},$$
--   and is in the small-degree regime $2 d^2 \le b$ (with $b \ge 1$), the derivative is uniformly bounded:
--   $$|Q'(c)| \;\le\; \frac{2 \, d^2}{b} \qquad \text{for every } c \in [0, b].$$
--
--   **Why the bundled $Q(0) = 0$ is essential.** Without it, the bound is *false*: take $Q(x) = x^2 / 36 - 17 x / 36 + 1$ (degree $d = 2$, grid size $b = 17$, regime $2 d^2 = 8 \le 17$ ✓). All $18$ grid values satisfy $|Q(j)| \le 1$, yet $|Q'(0)| = 17/36 \approx 0.4722 > 8/17 \approx 0.4706 = 2 d^2 / b$.
--
--   The constraint $Q(0) = 0$ tightens the bound by forcing the factorisation $Q(x) = x R(x)$ with $\deg R \le d - 1$, which constrains $Q'(0) = R(0)$ via the integer-grid bounds at $j = 1, 2, \ldots, b$.
--
--   This is the small-degree case of Nisan-Szegedy 1994 Lemma 2 (the large-degree case $2 d^2 > b$ being trivial since $b \le 2 d^2$ holds automatically there).
--
--   Left as a platform leaf — DEFERRED. Estimated 600-1000 Lean lines, may need its own decomposition into discrete-derivative bounds + classical Markov on intervals + a sharper continuous-extension lemma exploiting $Q(0) = 0$.
-- source:
--   Markov-Pólya inequality on the integer grid, with NS-bundled value constraint Q(0) = 0. See Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313, where the constraint Q(0) = 0 is essential for the sharp constant 2 d² / b. Without Q(0) = 0, the bound is false: Q(x) = x²/36 - 17x/36 + 1 (d=2, b=17, regime 2d²=8≤17) satisfies all 18 grid bounds |Q(j)| ≤ 1 but |Q'(0)| = 17/36 > 8/17 = 2 d²/b.

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

/-!
# Markov-Pólya inequality on the integer grid (NS-bundled form)

Replacement for the disproven `markov_polya_grid`. The previous statement
"For Q of degree ≤ d with `|Q(j)| ≤ 1` on `{0, …, b}` and `2 d² ≤ b`,
`|Q'(c)| ≤ 2 d² / b` on `[0, b]`" is *false* for arbitrary Q —
counter-example: `Q(x) = x²/36 - 17x/36 + 1` (degree `d = 2`, grid size
`b = 17`, regime `2 d² = 8 ≤ 17` ✓, but `|Q'(0)| = 17/36 ≈ 0.4722 >
8/17 ≈ 0.4706 = 2 d² / b`).

The fix is to bundle Nisan–Szegedy's value constraint `Q(0) = 0` into the
hypotheses. With this constraint, the polynomial is heavily restricted
(the slope at 0 becomes the leading-order coefficient under the
factorisation `Q(x) = x R(x)` with `R` of degree `≤ d - 1`), and the
sharp constant `2 d² / b` does hold.

Left as a platform leaf — DEFERRED. The decomposition into a
Coppersmith–Rivlin continuous extension + classical Markov-on-an-interval
DOES NOT compose to the bound `2 d² / b` directly without using `Q(0) = 0`,
so the previous L5 leaves (`polynomial_grid_continuous_extension`,
`markov_inequality_interval`) are orphaned by this reformulation.
-/

/-- **Markov-Pólya inequality (NS-bundled).** For univariate real polynomial
`Q` with `Q.natDegree ≤ d`, `Q(0) = 0`, `|Q(j)| ≤ 1` on `{0, 1, …, b}`
(with `b ≥ 1`), and `2 d² ≤ b`, the derivative is uniformly bounded by
`2 d² / b` on `[0, b]`. -/

theorem markov_polya_grid_v2
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_zero : Q.eval 0 = 0)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1)
    (h_regime : 2 * d^2 ≤ b) :
    ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 / (b : ℝ) := by sorry
