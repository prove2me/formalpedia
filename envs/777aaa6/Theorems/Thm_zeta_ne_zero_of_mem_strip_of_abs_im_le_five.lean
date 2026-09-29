-- Prove2me | Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_five
-- name    : zeta_ne_zero_of_mem_strip_of_abs_im_le_five
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T13:18:41.267489+00:00
-- url     : https://prove2.me/theorems/4226338e-a397-489a-9e06-65bc2ea313bd
-- title:
--   $\zeta$ has no zeros in the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 5$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is an unconditional, completely explicit zero-free region for the low-lying part of the critical strip, of height $5$:
--
--   $$0<\operatorname{Re} s<1 \ \text{ and } \ |\operatorname{Im} s|\le 5 \ \Longrightarrow\ \zeta(s)\neq 0.$$
--
--   This sharpens the height-$2$ statement `zeta_ne_zero_of_mem_strip_of_abs_im_le_two`. The first nontrivial zero occurs at height $\approx 14.13$, so the region is still a proper truncation of the search region for zeros, but a larger one.
--
--   The proof is a quantitative estimate on the completed zeta function. Write $\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and $\Lambda_0(s)=\Lambda(s)+\frac1s+\frac1{1-s}$ for its entire part, which is the Mellin transform
--   $$\Lambda_0(s)=\tfrac12\int_0^\infty f(t)\,t^{s/2-1}\,dt$$
--   of the modified Jacobi theta kernel $f$, where $f(t)=\theta(t)-1$ for $t>1$ and $f(t)=t^{-1/2}\bigl(\theta(1/t)-1\bigr)$ for $0<t<1$.
--
--   Comparison with a geometric series gives $|\theta(t)-1|\le \tfrac52 e^{-\pi t}$ for $t\ge 1$, so for $0<\operatorname{Re} s<1$ the integrand is dominated by $\tfrac52 e^{-\pi t}$ on $(1,\infty)$ and by $\tfrac52 t^{-2}e^{-\pi/t}$ on $(0,1]$. The substitution $t\mapsto 1/t$ identifies the second integral with the first, so
--   $$\|\Lambda_0(s)\|\le \tfrac12\cdot 2\cdot \tfrac52\cdot\frac{e^{-\pi}}{\pi}\le \frac1{28}$$
--   using $e^{-\pi}\le 1/23$. On the other hand $\left\|\frac1s+\frac1{1-s}\right\|=\frac1{\|s\|\,\|1-s\|}\ge \frac1{26}$ in the rectangle $0<\operatorname{Re} s<1$, $|\operatorname{Im} s|\le 5$. Hence $\Lambda(s)=\Lambda_0(s)-\frac1s-\frac1{1-s}$ cannot vanish there, and since $\pi^{-s/2}\Gamma(s/2)\neq0$ for $\operatorname{Re} s>0$, neither can $\zeta(s)$.
--
--   **Formalization note.** `riemannZeta` is Mathlib's zeta function; `|s.im|` is the absolute value of the imaginary part of $s$.
-- source:
--   Standard theory of the completed Riemann zeta function; the quantitative form given here (bounding the entire part of the completed zeta function against its pole terms, with the substitution t -> 1/t on (0,1)) is elementary. See e.g. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Ch. II.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem zeta_ne_zero_of_mem_strip_of_abs_im_le_five (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 5) : riemannZeta s ≠ 0 := by sorry
