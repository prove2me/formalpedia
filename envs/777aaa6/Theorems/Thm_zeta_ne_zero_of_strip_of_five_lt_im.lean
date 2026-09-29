-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_five_lt_im
-- name    : zeta_ne_zero_of_strip_of_five_lt_im
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T13:18:34.150884+00:00
-- url     : https://prove2.me/theorems/c7d4897d-260f-4a55-95fc-d2bb468a9e29
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ in the upper strip $\operatorname{Im} s>5$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero strictly to the right of the critical line inside the critical strip and above height $5$:
--
--   $$\tfrac12<\operatorname{Re} s<1 \ \text{ and } \ \operatorname{Im} s>5 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is **open**, and it is equivalent to the Riemann hypothesis. The unconditionally known facts reduce the hypothesis to exactly this region: non-vanishing on $\operatorname{Re} s\ge 1$ is classical; the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 5$ is zero-free by an explicit estimate on the completed zeta function; and the reflection identity $\zeta(\bar s)=\overline{\zeta(s)}$ transfers a zero with $\operatorname{Im} s<-5$ to one with $\operatorname{Im} s>5$. Hence non-vanishing in the region above implies $\zeta(s)\neq0$ for all $\operatorname{Re} s>\tfrac12$, which by the functional equation and the localisation of the nontrivial zeros in the critical strip is the Riemann hypothesis.
--
--   The lower limit $5$ cannot be raised much by the method that settles the rectangle: at the first nontrivial zero, of height $\approx 14.13$, the entire part $\Lambda_0$ of the completed zeta function is exactly equal to its pole terms $\frac1s+\frac1{1-s}$, so no bound of the form $\|\Lambda_0\|\le C$ with $C$ independent of $s$ can reach that height.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function.
-- source:
--   https://en.wikipedia.org/wiki/Riemann_hypothesis

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_five_lt_im (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 5 < s.im) : riemannZeta s ≠ 0 := by sorry
