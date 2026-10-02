-- Prove2me | Theorems.Thm_ZudilinZeta_params13_contour_formula
-- name    : ZudilinZeta.params13_contour_formula
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T09:05:15.889562+00:00
-- url     : https://prove2.me/theorems/46c0629d-60fd-42f8-945c-253c58f85a7a
-- title:
--   Contour representation of Zudilin's concrete linear forms
-- statement:
--   Let $F_n$ be Zudilin's linear form with $r=3$, $q=13$, $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$, and $\eta_j=25+j$ for $4\le j\le13$. Let $K_n$ and $J_n$ be the reflected Gamma kernel and vertical integral defined in the accompanying definition. For every integer $n\ge2$ and every complex $\tau$ satisfying $87\le\operatorname{Re}\tau\le87.5$,
--   $$
--   |F_n|=\frac{n}{2\pi}\left|\operatorname{Re}J_n(\tau)\right|,
--   \qquad
--   J_n(\tau)=\int_{\mathbb R}K_n(\tau+it)e^{-n\pi i(\tau+it)}\,dt.
--   $$
--   Here $F_n=\tfrac12\sum_{m=0}^{\infty}R_n''(m)$ uses the rational function in Zudilin's note. The identity connects these arithmetic linear forms to the explicit integral for which a saddle asymptotic is available. There is no restriction on $\operatorname{Im}\tau$; translating it changes only the parameterization of the vertical line.
-- source:
--   Derived specialization of W. Zudilin, One of the numbers zeta(5), zeta(7), zeta(9), zeta(11) is irrational, Russian Math. Surveys 56:4 (2001), pp.774-775, the displayed rational function and equation (2), and the parameter choice on p.775, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf. The contour argument is adapted from W. Zudilin, Irrationality of values of the Riemann zeta function, Izvestiya Math.66:3 (2002), Lemmas 2.3-2.4, pp.497-499, especially (2.5), (2.8)-(2.10), https://www.math.ru.nl/~zudilin/PS/zete_main.pdf. The present eta-parameter kernel and absolute-value normalization are a derived specialization, not a verbatim statement of Lemma 2.4.

import Definitions.Def_ZudilinZetaContourKernel
set_option autoImplicit false

theorem ZudilinZeta.params13_contour_formula (τ : ℂ) (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) (n : ℕ) (hn : 2 ≤ n) :
    |ZudilinZeta.F ZudilinZeta.params13 n| = (n : ℝ) / (2 * Real.pi) *
      |(ZudilinZeta.params13KernelIntegral n τ).re| := by sorry
