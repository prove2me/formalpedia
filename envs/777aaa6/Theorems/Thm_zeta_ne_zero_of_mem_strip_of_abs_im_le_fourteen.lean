-- Prove2me | Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen
-- name    : zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-22T09:11:04.177767+00:00
-- url     : https://prove2.me/theorems/4d03bd60-1927-4e1b-ad4a-fb46c8524f54
-- title:
--   Zero-free rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 14$ for $\zeta$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is an unconditional, explicit zero-free region for the low-lying part of the critical strip, of height $14$:
--
--   $$0<\operatorname{Re} s<1 \ \text{ and } \ |\operatorname{Im} s|\le 14 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   The lowest nontrivial zero of $\zeta$ is $\tfrac12 + i\,14.134725\ldots$, so $14$ is the largest integer height for which such a rectangle is zero-free. The statement is a finite, numerically checkable fact; it extends the platform's zero-free rectangles of heights $2$, $5$ and $6$ in this environment.
--
--   **Formalization Note.** `riemannZeta` is Mathlib's analytically continued zeta function; `s.re`, `s.im` are the real and imaginary parts of the complex number `s`, and `|s.im|` is the real absolute value.
-- source:
--   Classical: the first nontrivial zero of ζ has ordinate 14.134725…; see e.g. H. M. Edwards, Riemann's Zeta Function (1974), §6.6 (Gram's computation of the first zeros), and A. M. Odlyzko's tables of zeros. Cf. T. Tao et al., numerical verification of RH (Thm 1.5 bottom block 0 ≤ Im s ≤ 14).

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 14) : riemannZeta s ≠ 0 := by sorry
