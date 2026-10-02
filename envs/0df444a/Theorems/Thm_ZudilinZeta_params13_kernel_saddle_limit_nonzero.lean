-- Prove2me | Theorems.Thm_ZudilinZeta_params13_kernel_saddle_limit_nonzero
-- name    : ZudilinZeta.params13_kernel_saddle_limit_nonzero
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T09:47:47.040076+00:00
-- url     : https://prove2.me/theorems/ee3390b8-a915-4b3f-9225-820145769198
-- title:
--   A nonzero saddle asymptotic for Zudilin's concrete Gamma kernel
-- statement:
--   Use Zudilin's parameters $r=3$, $q=13$, $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$, and $\eta_j=25+j$ for $4\le j\le13$. Let $\tau$ be a root of the characteristic polynomial in the upper half-plane whose real part is maximal among upper-half-plane roots. Then $87\le\operatorname{Re}\tau\le87.5$, and there is a nonzero complex number $c$ such that
--   $$
--   \frac{n^7\sqrt n}{(2\pi)^5}e^{-nf_0(\tau)}J_n(\tau)\longrightarrow c
--   \quad(n\to\infty),
--   $$
--   where $J_n$ is the vertical integral of the explicit reflected Gamma kernel in the accompanying definition, and $f_0$ is Zudilin's saddle-value function.
--
--   This is the concrete analytic ingredient needed to obtain small nonzero linear forms from a contour representation. The statement concerns the kernel integral itself; it does not assert its equality with the arithmetic linear form $F_n$.
-- source:
--   Derived concrete saddle-integral statement for W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 20, printed p.33, using the parameter choice in W. Zudilin, One of the numbers zeta(5), zeta(7), zeta(9), zeta(11) is irrational (2001), printed p.775, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf. Compare W. Zudilin, Irrationality of values of the Riemann zeta function, https://www.math.ru.nl/~zudilin/PS/zete_main.pdf, Section 2, saddle-point analysis. The explicit integral normalization and certified saddle strip are proved auxiliary assertions, not quoted verbatim from Lemma 20.

import Definitions.Def_ZudilinZetaContourKernel
import Definitions.Def_ZudilinZetaAsymp
set_option autoImplicit false

theorem ZudilinZeta.params13_kernel_saddle_limit_nonzero (τ : ℂ)
    (hroot : ZudilinZeta.charPoly ZudilinZeta.params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, ZudilinZeta.charPoly ZudilinZeta.params13 σ = 0 →
      0 < σ.im → σ.re ≤ τ.re) :
    (87 ≤ τ.re ∧ τ.re ≤ 175 / 2) ∧ ∃ c : ℂ, c ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ =>
        ((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
          Complex.exp (-(n : ℂ) * ZudilinZeta.f0 ZudilinZeta.params13 τ) *
            ZudilinZeta.params13KernelIntegral n τ) Filter.atTop (nhds c) := by sorry
