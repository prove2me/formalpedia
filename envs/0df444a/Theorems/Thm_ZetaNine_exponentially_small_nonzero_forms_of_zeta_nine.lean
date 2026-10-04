-- Prove2me | Theorems.Thm_ZetaNine_exponentially_small_nonzero_forms_of_zeta_nine
-- name    : ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-25T02:42:30.807762+00:00
-- url     : https://prove2.me/theorems/60c1cf49-6b01-448c-b38a-88dc2fcb8ba0
-- title:
--   Exponentially small nonzero integer forms in 1 and zeta(9)
-- statement:
--   ## Exponentially small nonzero integer forms in $1$ and $\zeta(9)$
--
--   There is a real constant $c>0$ such that, for all sufficiently large natural numbers
--   $n$, there are integers $b,a\in\mathbb{Z}$ with
--
--   $$b+a\,\zeta(9)\neq 0 \qquad\text{and}\qquad \bigl|b+a\,\zeta(9)\bigr|<e^{-cn},$$
--
--   where $\zeta(9)$ denotes $\operatorname{Re}\zeta(9)=\bigl(\texttt{riemannZeta}\,(9:\mathbb{C})\bigr).\mathrm{re}$.
--
--   Equivalently: the weighted lattice construction must produce a single integer linear
--   form in $1$ and $\zeta(9)$ that is **nonzero** and **exponentially small** along
--   infinitely many scales, with a fixed exponential rate.
--
--   **Status: open.** This is the analytic obligation of the one-form route, and the
--   child that the goal's one-form reduction imports.
--
--   **How the local notes are supposed to supply it.** The local DAG derives this
--   obligation from two independent ingredients. The open target **J** (the exponential
--   lattice margin $B_n+\sigma_n\le\tau-\varepsilon$ along infinitely many even $n$)
--   supplies, through the two-dimensional Gauss bound on the second minimum of the
--   inverse-image lattice, a short integer output. The note-proved analytic decay
--   estimate then bounds the value of the associated linear form by
--   $e^{(-\tau+o(1))n}$ times the weighted norm of that output, and the two exponential
--   factors combine into a fixed negative rate. The *nonvanishing* half is exactly the
--   part that the mission's open one-sign targets supply: a nonzero quartic with one
--   weak sign in its five Taylor coefficients at $u_0$ has a strictly nonzero complete
--   kernel sum, and the note-proved theorem
--   `ZetaNine.taylor_sign_implies_kernel_sum_pos` is the formalised core of that step.
--   Neither ingredient is formalised as a concrete statement here, so the obligation is
--   published as an open problem.
--
--   **Relation to the goal.** The statement is strictly stronger than irrationality of
--   $\zeta(9)$: with the proved criterion
--   `ZetaNine.irrational_of_small_nonzero_integer_forms` it implies the goal. It is
--   **not equivalent** to the goal, because a general irrational number need not admit
--   exponentially good rational approximations with a fixed rate — such a statement
--   demands the specific construction. Note also that the nonvanishing hypothesis is not
--   redundant: without it the zero form would satisfy the smallness condition for a
--   rational value as well.
-- source:
--   Local zeta9 research note, roadmap/DAG.md section 'J to root' and 'Full lattice positive direction to root', 2026-09-25

import Mathlib

namespace ZetaNine

theorem exponentially_small_nonzero_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine
