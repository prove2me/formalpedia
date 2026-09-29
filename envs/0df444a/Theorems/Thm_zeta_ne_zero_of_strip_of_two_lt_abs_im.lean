-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_abs_im
-- name    : zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T12:02:43.796488+00:00
-- url     : https://prove2.me/theorems/f529e6fa-18de-4508-950e-9ba193f8af8d
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ above height $2$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero strictly to the right of the critical line inside the critical strip, at height larger than $2$:
--
--   $$\tfrac12<\operatorname{Re} s<1 \ \text{ and } \ |\operatorname{Im} s|>2 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is **open**: it is the Riemann hypothesis with the two parts that are unconditionally known removed. Indeed, non-vanishing for $\operatorname{Re} s\ge 1$ is classical (Mathlib's `riemannZeta_ne_zero_of_one_le_re`), and non-vanishing in the low-lying rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 2$ is an explicit estimate on the completed zeta function. Together with those two facts, the statement above is equivalent to the half-plane form of the Riemann hypothesis, $\operatorname{Re} s>\tfrac12\Rightarrow\zeta(s)\neq 0$, and hence to the Riemann hypothesis itself.
--
--   Phrasing the remaining open problem this way isolates exactly the region where the difficulty lies: a bounded-real-part, unbounded-height region on one side of the critical line. Any progress of zero-density or zero-free-region type applies to it directly.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function; `|s.im|` is the absolute value of the imaginary part of $s$.
-- source:
--   https://en.wikipedia.org/wiki/Riemann_hypothesis

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_two_lt_abs_im (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < |s.im|) : riemannZeta s ≠ 0 := by sorry
