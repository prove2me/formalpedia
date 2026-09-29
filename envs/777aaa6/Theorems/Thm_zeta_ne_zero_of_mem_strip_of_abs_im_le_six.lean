-- Prove2me | Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_six
-- name    : zeta_ne_zero_of_mem_strip_of_abs_im_le_six
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T13:49:30.687503+00:00
-- url     : https://prove2.me/theorems/785b8b9a-c19b-4509-80e2-e9bb25ec8c90
-- title:
--   $\zeta$ has no zeros in the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 6$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is an unconditional, completely explicit zero-free region for the low-lying part of the critical strip, of height $6$:
--
--   $$0<\operatorname{Re} s<1 \ \text{ and } \ |\operatorname{Im} s|\le 6 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   The first nontrivial zero occurs at height $\approx 14.13$, so this is a proper truncation of the region in which zeros must be sought.
--
--   The proof is a quantitative estimate on the completed zeta function. Write $\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and $\Lambda_0(s)=\Lambda(s)+\frac1s+\frac1{1-s}$ for its entire part, which is the Mellin transform
--   $$\Lambda_0(s)=\tfrac12\int_0^\infty f(t)\,t^{s/2-1}\,dt$$
--   of the modified Jacobi theta kernel $f$, with $f(t)=\theta(t)-1$ for $t>1$ and $f(t)=t^{-1/2}(\theta(1/t)-1)$ for $0<t<1$.
--
--   Comparison with a geometric series gives $|\theta(t)-1|\le \tfrac{21}{10}e^{-\pi t}$ for $t\ge1$, so for $0<\operatorname{Re} s<1$ the Mellin integrand is dominated by $\tfrac{21}{10}t^{-1/2}e^{-\pi t}$ on $(1,\infty)$ and by $\tfrac{21}{10}t^{-3/2}e^{-\pi/t}$ on $(0,1]$; the substitution $t\mapsto 1/t$ identifies the second integral with the first. Hence
--   $$\|\Lambda_0(s)\|\le \frac{21}{10}\int_1^\infty u^{-1/2}e^{-\pi u}\,du\le 0.0268,$$
--   the tail integral being estimated by the elementary inequality $u^{-1/2}\le 1-\tfrac{u-1}{2}+\tfrac38 (u-1)^2$. On the other hand, in the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 6$ one has $\|s\|\,\|1-s\|\le\sqrt{36\cdot 37}<36.5$, so
--   $$\left\|\frac1s+\frac1{1-s}\right\|=\frac1{\|s\|\,\|1-s\|}>\frac1{36.5}>0.0268 .$$
--   Therefore $\Lambda(s)=\Lambda_0(s)-\frac1s-\frac1{1-s}$ cannot vanish in the rectangle, and since $\pi^{-s/2}\Gamma(s/2)\neq0$ for $\operatorname{Re} s>0$, neither can $\zeta(s)$.
--
--   Height $6$ is close to the ceiling of this method: with the exact constants $2/(1-e^{-\pi})$ and $\int_1^\infty u^{-1/2}e^{-\pi u}du=0.012178\ldots$ one gets $\|\Lambda_0\|\le 0.02547$, which fails once $\|s\|\|1-s\|\ge 39.3$, i.e. above height $\approx 6.2$.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function; `|s.im|` is the absolute value of the imaginary part of $s$.
-- source:
--   Standard theory of the completed Riemann zeta function; the quantitative form given here (bounding the entire part of the completed zeta function against its pole terms, with the substitution t -> 1/t on (0,1) and the tail bound for the incomplete Gamma integral) is elementary. See e.g. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Ch. II.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_mem_strip_of_abs_im_le_six (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 6) : riemannZeta s ≠ 0 := by sorry
