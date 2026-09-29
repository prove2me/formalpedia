-- Prove2me | Theorems.Thm_irrational_or_irrational_of_int_linear_forms
-- name    : irrational_or_irrational_of_int_linear_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T23:37:14.522424+00:00
-- url     : https://prove2.me/theorems/34f9c72a-f38c-468c-9367-c9be62e13091
-- title:
--   Two-variable irrationality criterion from vanishing integer linear forms
-- statement:
--   Suppose there are integer sequences $(A_n), (B_n), (C_n)$ such that the linear forms
--
--   $$L_n \;=\; A_n x + B_n y + C_n$$
--
--   never vanish and satisfy $L_n \to 0$. Then at least one of $x$, $y$ is irrational.
--
--   The proof is the two-variable form of the classical criterion. If both $x = a/b$ and $y = c/d$ were rational, then with $D = bd$ every form would be an integer over the single fixed denominator $D$,
--
--   $$L_n \;=\; \frac{A_n a d + B_n c b + C_n D}{D},$$
--
--   whose numerator is a non-zero integer by hypothesis. Hence $|L_n| \ge 1/D > 0$ for every $n$, a bound independent of $n$, contradicting $L_n \to 0$.
--
--   **Why the two-variable form is the one that matters.** For a single constant, the corresponding criterion is *equivalent* to irrationality — Dirichlet's approximation theorem supplies the converse — so an existential statement about forms in one variable is a restatement of the problem rather than a subgoal. The same is true of the two-variable existential. What is not a restatement is the assertion that a **specific, explicitly constructed** sequence has these properties, and this lemma is the socket such a construction plugs into.
--
--   That is exactly the shape of the known results on Euler's constant. Aptekarev's construction produces linear forms in $1$, $\gamma$ and the Euler--Gompertz constant $\delta$ from a third-order linear recurrence with polynomial coefficients; feeding those forms into this lemma yields the disjunction "at least one of $\gamma$, $\delta$ is irrational". The forms do not separate the two constants, which is precisely why the conclusion is a disjunction and not a verdict on $\gamma$.
-- source:
--   Classical two-variable irrationality criterion; the form in which the disjunctive results on Euler's constant and the Euler-Gompertz constant are obtained, e.g. A. I. Aptekarev, On linear forms containing the Euler constant, https://arxiv.org/abs/0902.1768.

import Mathlib

theorem irrational_or_irrational_of_int_linear_forms (x y : ℝ) (A B C : ℕ → ℤ)
    (hne : ∀ n, (A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational x ∨ Irrational y := by sorry
