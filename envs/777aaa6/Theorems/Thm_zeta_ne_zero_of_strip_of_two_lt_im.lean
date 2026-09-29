-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_im
-- name    : zeta_ne_zero_of_strip_of_two_lt_im
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T12:28:22.706029+00:00
-- url     : https://prove2.me/theorems/661c33b7-b606-41a9-8765-2ec2a07e824e
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ in the upper strip $\operatorname{Im} s>2$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero strictly to the right of the critical line inside the critical strip and above height $2$:
--
--   $$\tfrac12<\operatorname{Re} s<1 \ \text{ and } \ \operatorname{Im} s>2 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is **open**, and it is equivalent to the Riemann hypothesis. Indeed, the three facts that are unconditionally known reduce the hypothesis to exactly this region: non-vanishing on $\operatorname{Re} s\ge 1$ is classical; the low-lying rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 2$ is zero-free by an explicit estimate on the completed zeta function; and the reflection identity $\zeta(\bar s)=\overline{\zeta(s)}$ transfers a zero with $\operatorname{Im} s<-2$ to one with $\operatorname{Im} s>2$. Hence non-vanishing in the region above implies $\zeta(s)\neq 0$ for all $\operatorname{Re} s>\tfrac12$, which by the functional equation and the localisation of the nontrivial zeros in the critical strip is the Riemann hypothesis.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function.
-- source:
--   https://en.wikipedia.org/wiki/Riemann_hypothesis

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_two_lt_im (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < s.im) : riemannZeta s ≠ 0 := by sorry
