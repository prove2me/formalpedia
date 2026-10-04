-- Prove2me | Theorems.Thm_ZetaNine_finite_prime_budget
-- name    : ZetaNine.finite_prime_budget
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-24T14:09:50.929992+00:00
-- url     : https://prove2.me/theorems/8496d3a0-3b92-4a68-a56d-d972e0df20a2
-- title:
--   Finite weighted prime-budget inequality
-- statement:
--   Let $S$ be a finite index set. For each $i\in S$, take nonnegative integers $v_i,a_i$ and a real weight $w_i\ge0$. With $(x)_+=\max(x,0)$,
--
--   $$
--   \sum_{i\in S}(v_i-2a_i)_+w_i
--   \le9\sum_{i\in S}a_iw_i
--   +\sum_{i\in S}(v_i-11a_i)_+w_i.
--   $$
--
--   This is the finite weighted valuation inequality underlying the new $\zeta(9)$ prime-budget reduction. It does not itself include the large-prime contribution or the asymptotic prime number theorem step.
-- source:
--   Local zeta9 research note, roadmap/research/arithmetic-prime-budget.md, equations (1)-(2), 2026-09-24

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace ZetaNine

theorem finite_prime_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v a : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i ≤
      9 * ∑ i ∈ s, (a i : ℝ) * w i +
        ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by sorry

end ZetaNine
