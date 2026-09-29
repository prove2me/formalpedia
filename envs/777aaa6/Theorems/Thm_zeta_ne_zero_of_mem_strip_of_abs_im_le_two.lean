-- Prove2me | Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
-- name    : zeta_ne_zero_of_mem_strip_of_abs_im_le_two
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T12:08:46.92829+00:00
-- url     : https://prove2.me/theorems/1198a0c7-feb8-4067-b324-c43429da028e
-- title:
--   $\zeta$ has no zeros in the low-lying rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 2$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is an unconditional, completely explicit zero-free region for the low-lying part of the critical strip:
--
--   $$0<\operatorname{Re} s<1 \ \text{ and } \ |\operatorname{Im} s|\le 2 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   In particular $\zeta$ does not vanish anywhere on the real segment $(0,1)$, nor at any point of the critical line of height at most $2$; the first nontrivial zero occurs at height $\approx 14.13$, so the statement is a (modest) truncation of the region where zeros must be searched for.
--
--   The statement is provable from the standard theory of the completed zeta function. Write $\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)$ for the completed zeta function and $\Lambda_0(s)=\Lambda(s)+\frac1s+\frac{1}{1-s}$ for its entire part, which is the Mellin transform of the modified Jacobi theta kernel. Because the theta kernel decays like $e^{-\pi t}$, one obtains a completely explicit bound of the form $\|\Lambda_0(s)\|\le \tfrac18$ valid throughout the strip $0<\operatorname{Re} s<1$, whereas the pole terms satisfy
--
--   $$\left\|\frac1s+\frac{1}{1-s}\right\| = \frac{1}{\|s\|\,\|1-s\|}\ \ge\ \frac15$$
--
--   in the rectangle. Hence $\Lambda(s)=\Lambda_0(s)-\frac1s-\frac{1}{1-s}$ cannot vanish there, and since $\pi^{-s/2}\Gamma(s/2)\neq 0$ for $\operatorname{Re} s>0$, neither can $\zeta(s)$.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function; `|s.im|` is the absolute value of the imaginary part of $s$.
-- source:
--   Standard theory of the completed Riemann zeta function; the quantitative form given here (bounding the entire part of the completed zeta function against its pole terms) is elementary. See e.g. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Ch. II.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_mem_strip_of_abs_im_le_two (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 2) : riemannZeta s ≠ 0 := by sorry
