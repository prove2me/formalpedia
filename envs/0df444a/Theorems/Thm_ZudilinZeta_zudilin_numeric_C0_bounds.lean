-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds
-- name    : ZudilinZeta.zudilin_numeric_C0_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T17:08:29.022905+00:00
-- url     : https://prove2.me/theorems/3180ae81-430b-4d26-81c0-cfe84e9b83dd
-- title:
--   Certified enclosure of the analytic constant C₀ for Zudilin’s parameters
-- statement:
--   For the parameters $r=3$, $q=13$, $\eta_0=91$, $\eta_1=\eta_2=\eta_3=27$, and $\eta_j=25+j$ for $4\le j\le13$, let $\tau$ be any root of the characteristic polynomial in the upper half-plane whose real part is maximal among upper-half-plane roots. Then the analytic constant $C_0=-\operatorname{Re}f_0(\tau)$ satisfies
--   $$227.58019641\le C_0<227.58019642.$$
--   This is the analytic half of the numerical comparison in the proof of Zudilin’s theorem. The enclosure is uniform over every root satisfying the maximality condition, rather than an assumed decimal approximation to a chosen root.
-- source:
--   W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Proposition 5 and proof of Theorem 3, printed pp. 34–35; the analytic constant is C0, and that paper denotes the mission arithmetic constant C1 by C2. Also One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), 774–776.

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem zudilin_numeric_C0_bounds (τ : ℂ) (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    227.58019641 ≤ C0 params13 τ ∧ C0 params13 τ < 227.58019642 := by sorry
end ZudilinZeta
