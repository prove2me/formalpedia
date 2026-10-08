-- Prove2me | Theorems.Thm_ConvexOptimization_two_phase_iteration_count_of_suboptimality
-- name    : ConvexOptimization.two_phase_iteration_count_of_suboptimality
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T08:29:21.524519+00:00
-- url     : https://prove2.me/theorems/cb8a78ec-670a-4336-9334-d9d82bbc8843
-- title:
--   Two-phase iteration count from a residual certificate
-- statement:
--   Let $a_k\ge0$ be an objective gap and $q_k\ge0$ a phase-detecting residual. Fix positive constants $m,\gamma,s,\eta,\varepsilon_0,\varepsilon$ such that $\varepsilon\le\varepsilon_0/4$,
--
--   $$
--   \varepsilon_0s^2=\frac1{2m},\qquad s\eta\le\frac12,
--   $$
--
--   and assume the certificate
--
--   $$
--   a_k\le\frac{q_k^2}{2m}.
--   $$
--
--   Suppose that above the threshold the gap decreases by a fixed amount,
--
--   $$
--   q_k\ge\eta\Longrightarrow a_{k+1}\le a_k-\gamma,
--   $$
--
--   and below the threshold the scaled residual squares,
--
--   $$
--   q_k<\eta\Longrightarrow s q_{k+1}\le(sq_k)^2.
--   $$
--
--   Then every $K\in\mathbb{N}$ satisfying
--
--   $$
--   K\ge\frac{a_0}{\gamma}+\log_2\!\log_2\!\left(\frac{\varepsilon_0}{\varepsilon}\right)
--   $$
--
--   satisfies $a_K\le\varepsilon$.
--
--   This is the reusable discrete bookkeeping theorem behind the two-phase Newton complexity estimate: fixed decrease bounds the damped phase, while repeated squaring produces the doubly logarithmic quadratic-phase budget.
-- source:
--   Boyd and Vandenberghe, Convex Optimization, Cambridge University Press, 2004 (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf, section 9.5.3, pp. 488-489, equations (9.32)-(9.36).

import Mathlib

theorem ConvexOptimization.two_phase_iteration_count_of_suboptimality
    (gap measure : ℕ → ℝ) (m decrease scale threshold ε₀ ε : ℝ)
    (hm : 0 < m) (hdecrease : 0 < decrease) (hscale : 0 < scale)
    (hthreshold : 0 < threshold) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hεsmall : ε ≤ ε₀ / 4)
    (hnormalization : ε₀ * scale ^ 2 = 1 / (2 * m))
    (hscaledThreshold : scale * threshold ≤ 1 / 2)
    (hgap_nonneg : ∀ k, 0 ≤ gap k)
    (hmeasure_nonneg : ∀ k, 0 ≤ measure k)
    (hdamped : ∀ k, threshold ≤ measure k →
      gap (k + 1) ≤ gap k - decrease)
    (hquadratic : ∀ k, measure k < threshold →
      scale * measure (k + 1) ≤ (scale * measure k) ^ 2)
    (hsuboptimality : ∀ k, gap k ≤ measure k ^ 2 / (2 * m))
    (K : ℕ)
    (hK : gap 0 / decrease +
      Real.logb 2 (Real.logb 2 (ε₀ / ε)) ≤ (K : ℝ)) :
    gap K ≤ ε := by
  sorry
