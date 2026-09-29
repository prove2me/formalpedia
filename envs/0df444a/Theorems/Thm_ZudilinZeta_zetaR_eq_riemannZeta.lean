-- Prove2me | Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta
-- name    : ZudilinZeta.zetaR_eq_riemannZeta
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T14:51:08.1138+00:00
-- url     : https://prove2.me/theorems/1099a3e9-706e-4903-a3f5-bff4120ac4a6
-- title:
--   The series $\operatorname{zetaR} k = \sum_n (n+1)^{-k}$ equals Mathlib's `riemannZeta` at integers $k \geq 2$
-- statement:
--   For every integer $k \geq 2$ the absolutely convergent Dirichlet series
--   $$\zeta(k) = \sum_{n=1}^\infty \frac{1}{n^k} = \sum_{n=0}^\infty \frac{1}{(n+1)^k}$$
--   is the value of Riemann's zeta function at the integer $k$. The statement bridges the elementary series `ZudilinZeta.zetaR k` (used throughout the `ZudilinZeta` formalization of the irrationality linear forms) with Mathlib's complex `riemannZeta`, which is the function occurring in the mission goal `FCP.Zeta.zudilin_five_seven_nine_eleven`. The identification holds because both sides are given by the same Dirichlet series at $k \geq 2$ (Euler's definition; see Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow` in Mathlib/NumberTheory/LSeries/RiemannZeta.lean).
-- source:
--   L. Euler, De summis serierum reciprocarum (1735); the Dirichlet-series identity for the Riemann zeta function, e.g. E. C. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Oxford, 1986, §1; formalized in Mathlib/NumberTheory/LSeries/RiemannZeta.lean as zeta_eq_tsum_one_div_nat_add_one_cpow.

import Mathlib
import Definitions.Def_ZudilinZetaSetup

namespace ZudilinZeta
theorem zetaR_eq_riemannZeta (k : ℕ) (hk : 2 ≤ k) :
    riemannZeta (k : ℂ) = (zetaR k : ℂ) := by sorry
end ZudilinZeta
