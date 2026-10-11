-- Prove2me | Theorems.Thm_ZetaEM_riemannZeta_eq_euler_maclaurin_nu_one
-- name    : ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-10T18:55:09.612339+00:00
-- url     : https://prove2.me/theorems/1c58dd45-a480-4fb1-a664-080de2fc8d35
-- title:
--   Euler–Maclaurin formula for $\zeta(s)$ with remainder in $\bar B_3$ (case $\nu=1$), $\operatorname{Re}(s)>0$
-- statement:
--   **Euler–Maclaurin evaluation of $\zeta(s)$ with one Bernoulli correction.** For every integer $N\ge 1$ and every $s\in\mathbb C$ with $\operatorname{Re}(s)>0$ and $s\neq 1$,
--
--   $$\zeta(s)=\sum_{n=1}^{N} n^{-s}-\frac{N^{1-s}}{1-s}-\frac{N^{-s}}{2}+\frac{s\,N^{-s-1}}{12}-\frac{s(s+1)(s+2)}{6}\int_N^{\infty}\bar B_3(x)\,x^{-s-3}\,dx,$$
--
--   where $\bar B_3(x)=B_3(\{x\})$ is the periodic third Bernoulli function, $B_3(y)=y^3-\tfrac32y^2+\tfrac12y$ and $\{x\}=x-\lfloor x\rfloor$. In Lean: `riemannZeta` is Mathlib's $\zeta$ (its analytic continuation), $\bar B_3(x)$ is `bernoulliFun 3 (Int.fract x)`, and the powers are Mathlib's complex powers (`cpow`) of the positive reals $n$, $N$, $x$.
--
--   This is the case $\nu=1$ of the Euler–Maclaurin evaluation of $\zeta(s)$ in Edwards, *Riemann's Zeta Function*, §6.4 (equivalently DLMF (25.2.8) with $n=1$), restricted to $\operatorname{Re}(s)>0$; the source formula holds for $\operatorname{Re}(s)>-2$.
--
--   Role: this identity, taken at $N=10$, is the only analytic input of the parent theorem `TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen` ($\zeta(s)\neq0$ for $0<\operatorname{Re}(s)<1$, $2\le\operatorname{Im}(s)\le14$). The parent bounds the integral term explicitly and certifies, by kernel-checked interval arithmetic on 638 boxes covering $6\le\operatorname{Im}(s)\le14$, that the main terms stay farther from $0$ than that bound; the range $2\le\operatorname{Im}(s)\le6$ comes from the proved theorem `ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six`.
--
--   **Formalization Note**: Edwards writes the main part as $\sum_{n=1}^{N-1}n^{-s}+\frac{N^{1-s}}{s-1}+\frac12N^{-s}$, which equals the first three terms above. The sum $\sum_{n\in[1,N]}$ binds only $n^{-s}$. The integral is the Lebesgue (Bochner) integral over $(N,\infty)$; it converges absolutely for $\operatorname{Re}(s)>-2$.
-- source:
--   H. M. Edwards, Riemann's Zeta Function, Academic Press, New York, 1974 (unabridged Dover reprint 2001), Chapter 6, Section 6.4 "Evaluation of zeta by Euler-Maclaurin summation", p. 114: the formula for zeta(s) with remainder R_{2nu}, case nu = 1. Same identity: NIST DLMF Eq. (25.2.8) with n = 1, https://dlmf.nist.gov/25.2.E8

import Mathlib

theorem ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s)
      - (N : ℂ) ^ (-s) / 2 + s * (N : ℂ) ^ (-s - 1) / 12
      - s * (s + 1) * (s + 2) / 6 *
          ∫ x in Set.Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3) := by sorry
