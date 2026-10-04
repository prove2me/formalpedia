-- Prove2me | Theorems.Thm_ZetaNine_exponentially_small_independent_forms_of_zeta_nine
-- name    : ZetaNine.exponentially_small_independent_forms_of_zeta_nine
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-25T02:42:32.712136+00:00
-- url     : https://prove2.me/theorems/691b1665-f122-47f7-a3e4-2c28a06055f2
-- title:
--   Exponentially small independent integer forms in 1 and zeta(9)
-- statement:
--   ## Exponentially small independent integer forms in $1$ and $\zeta(9)$
--
--   There is a real constant $c>0$ such that, for all sufficiently large natural numbers
--   $n$, there are integers $b_1,a_1,b_2,a_2\in\mathbb{Z}$ with
--
--   $$b_1a_2\neq b_2a_1,\qquad
--   \bigl|b_1+a_1\,\zeta(9)\bigr|<e^{-cn},\qquad
--   \bigl|b_2+a_2\,\zeta(9)\bigr|<e^{-cn},$$
--
--   where $\zeta(9)=\bigl(\texttt{riemannZeta}\,(9:\mathbb{C})\bigr).\mathrm{re}$ and
--   $c>0$ is a fixed exponential rate.
--
--   **Status: open.** This is the analytic obligation of the mission's main (two-form)
--   route and the child that the goal's two-form reduction imports.
--
--   **How the local notes are supposed to supply it.** This is the two-form version of
--   the previous obligation. The open target **J** gives, by the two-dimensional Gauss
--   bound for the second successive minimum of the inverse-image lattice, two integer
--   outputs whose weighted norms are $\le e^{(\tau-\varepsilon/2)n}$; because the
--   inverse image $E_n$ is injective, the two outputs are independent and so the two
--   linear forms are non-proportional. The note-proved uniform analytic decay estimate
--   then makes both values exponentially small with the same rate. Neither the lattice
--   statement nor the decay estimate is formalised concretely here.
--
--   **Relation to the goal.** With the proved criterion
--   `ZetaNine.irrational_of_two_small_integer_forms` this obligation implies the goal.
--   It is the more demanding of the two published obligations because it requires two
--   non-proportional forms along the **same** sequence of scales, rather than one form
--   with a nonvanishing certificate.
--
--   **Note on the missing nonvanishing clause.** Unlike the one-form obligation, this
--   statement does not require either form to be nonzero. That is intentional and
--   sufficient: if both forms $b_i+a_i\,\zeta(9)$ vanished, then both coefficient vectors
--   $(b_i,a_i)$ would lie in the span of $(-x,1)$ with $x=\zeta(9)$ (a vanishing form
--   with $x=0$ has $b_i=0$ and the vector is again in that span), so
--   $b_1a_2-b_2a_1=0$. Independence therefore already forces at least one form to be
--   nonzero, which is precisely the hypothesis consumed by the two-form criterion;
--   adding a nonvanishing clause would duplicate a consequence.
-- source:
--   Local zeta9 research note, roadmap/DAG.md section 'J to root' and roadmap/research/arithmetic.md two-dimensional Gauss bound, 2026-09-25

import Mathlib

namespace ZetaNine

theorem exponentially_small_independent_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine
