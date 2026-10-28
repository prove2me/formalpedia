-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_fourteen_lt_im
-- name    : zeta_ne_zero_of_strip_of_fourteen_lt_im
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:11:05.663397+00:00
-- url     : https://prove2.me/theorems/7ac15c26-d354-4673-bdf0-ee0f7666443a
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ above height $14$ (equivalent to RH)
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero strictly to the right of the critical line inside the critical strip and above height $14$:
--
--   $$\tfrac12<\operatorname{Re} s<1 \ \text{ and } \ \operatorname{Im} s>14 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is **open**, and it is equivalent to the Riemann hypothesis. The unconditionally known facts reduce the hypothesis to exactly this region: non-vanishing on $\operatorname{Re} s\ge1$ is classical; the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 14$ is zero-free (the first nontrivial zero has ordinate $14.1347\ldots$); the functional equation maps zeros with $0<\operatorname{Re}s<\tfrac12$ to zeros with $\tfrac12<\operatorname{Re}s<1$; and the reflection identity $\zeta(\bar s)=\overline{\zeta(s)}$ transfers a zero with $\operatorname{Im} s<-14$ to one with $\operatorname{Im} s>14$. It is the height-$14$ member of the family of statements `zeta_ne_zero_of_strip_of_*_lt_im` (heights $2$, $5$, $6$) on the platform; the larger threshold makes it formally weaker than those, and the gap is filled by the zero-free rectangle of height $14$.
--
--   **Formalization Note.** `riemannZeta` is Mathlib's analytically continued zeta function; `s.re`, `s.im` are the real and imaginary parts of `s`.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed. (rev. D. R. Heath-Brown), Oxford 1986, Ch. 14 (the Riemann hypothesis), with the reduction to Re s > 1/2 via the functional equation (§2.1) and the first zero at height 14.1347 (§15).

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_fourteen_lt_im (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 14 < s.im) : riemannZeta s ≠ 0 := by sorry
