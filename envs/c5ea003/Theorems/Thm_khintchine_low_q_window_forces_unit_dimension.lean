-- Prove2me | Theorems.Thm_khintchine_low_q_window_forces_unit_dimension
-- name    : khintchine_low_q_window_forces_unit_dimension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T20:55:18.760099+00:00
-- url     : https://prove2.me/theorems/9fe21e50-d275-4e1e-8dce-afae7798579f
-- statement:
--   **Low-$q$ logarithmic-window arithmetic.**
--
--   Let $q\in\mathbb N$ satisfy
--   $$
--   1\le q,\qquad \neg(2\le q),\qquad q\ge \beta\log(\max\{n_1,n_2\}),\qquad \beta>2.
--   $$
--   Since $q$ is an integer, the first two inequalities force $q=1$.  The displayed logarithmic window can then hold only when
--   $$
--   \max\{n_1,n_2\}\le 1.
--   $$
--   Indeed, if $\max\{n_1,n_2\}\ge2$, monotonicity of $\log$ gives $\log(\max\{n_1,n_2\})\ge\log2$, and $\beta>2$ gives $\beta\log2>1$, contradicting $q=1$.
--
--   Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 24, together with the surrounding Schatten-moment condition $q\ge\beta\log n$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem khintchine_low_q_window_forces_unit_dimension :
    ∀ (β : ℝ), 2 < β →
    ∀ (n₁ n₂ q : ℕ),
      1 ≤ q →
      ¬ 2 ≤ q →
      (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
      max n₁ n₂ ≤ 1 := by
  sorry
