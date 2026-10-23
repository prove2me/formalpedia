-- Prove2me | Theorems.Thm_zeta_ne_zero_of_strip_of_hundred_six_lt_im
-- name    : zeta_ne_zero_of_strip_of_hundred_six_lt_im
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-22T11:42:00.387812+00:00
-- url     : https://prove2.me/theorems/0144fc11-88f4-4dc1-8346-db866cf341eb
-- title:
--   No zeros of $\zeta$ with $\tfrac12<\operatorname{Re} s<1$ above height $106$ (equivalent to RH)
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero strictly to the right of the critical line inside the critical strip and above height $106$:
--
--   $$\tfrac12<\operatorname{Re} s<1 \ \text{ and } \ \operatorname{Im} s>106 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This is **open**, and it is equivalent to the Riemann hypothesis: the region with $\operatorname{Im} s\le 106$ is already certified in this mission's tree (heights $\le 14$ zero-free, $14$ to $100$ and $100$ to $106$ verified slices), the region $\operatorname{Re} s\ge 1$ is zero-free, and zeros are symmetric under $s\mapsto 1-\bar s$ and $s\mapsto\bar s$.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed. (rev. D. R. Heath-Brown), Oxford 1986, Ch. 14 (the Riemann hypothesis), with the reduction to Re s > 1/2 via the functional equation (§2.1). This is the remaining part of zeta_ne_zero_of_strip_of_hundred_lt_im after the certified range 100 < Im s <= 106.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_strip_of_hundred_six_lt_im (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 106 < s.im) : riemannZeta s ≠ 0 := by sorry
