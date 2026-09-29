-- Prove2me | Theorems.Thm_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
-- name    : exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f74ef561-58c9-5e9f-803d-e5f04da87f04
-- title:
--   Uniform bound |logμ(x)|≤ c (-logμ(p)) for algebraic x
-- statement:
--   Let $K$ be a field of characteristic zero, let $x \in K$ be nonzero and algebraic over $\mathbb{Q}$ (in the sense that $x$ is a root of a nonzero polynomial with rational coefficients, under the canonical map $\mathbb{Q} \to K$), and let $p$ be a prime natural number. The assertion is the existence of a real constant $c \ge 0$, depending only on $x$ and $p$, with the following uniformity property: for every real-valued absolute value $\mu$ on $K$ which is non-archimedean, i.e. satisfies $\mu(a+b) \le \max(\mu(a),\mu(b))$ for all $a,b \in K$, and which satisfies $\mu(p) < 1$ for the image of $p$ in $K$, one has $$|\log \mu(x)| \le c\,\bigl(-\log \mu(p)\bigr).$$ Note that $\mu(p) < 1$ together with $\mu(p) > 0$ makes the right-hand side a nonnegative multiple of $c$, so the inequality bounds $\log\mu(x)$ above and below simultaneously; the point is that $c$ is independent of $\mu$, so in particular the bound is invariant under replacing $\mu$ by a power $\mu^t$.
--
--   This is the elementary valuation-theoretic statement that a fixed nonzero algebraic number has logarithmic size $O(-\log\mu(p))$ uniformly over all non-archimedean absolute values lying over $p$; no classification of absolute values is involved. It is used in the analysis of absolute values of values of modular functions on $X_0(N)$, for instance in [`ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox`](thm.html#ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox), [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot) and [`ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox`](thm.html#ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox), where constants attached to fixed algebraic data must be expressed homogeneously in $-\log\mu(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
    {K : Type*} [Field K] [CharZero K] (x : K) (hx0 : x ≠ 0) (hx : IsAlgebraic ℚ x)
    (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue K ℝ, IsNonarchimedean μ → μ (p : K) < 1 →
      |Real.log (μ x)| ≤ c * (-Real.log (μ (p : K))) := by sorry
