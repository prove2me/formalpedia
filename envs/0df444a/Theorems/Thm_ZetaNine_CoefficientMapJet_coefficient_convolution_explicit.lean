-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapJet_coefficient_convolution_explicit
-- name    : ZetaNine.CoefficientMapJet.coefficient_convolution_explicit
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T16:07:05.364069+00:00
-- url     : https://prove2.me/theorems/3c3fe37c-b5a4-4ecc-b741-18ddee5254de
-- title:
--   All nine actual local coefficient convolutions
-- statement:
--   Let $n,j,s$ be natural numbers with $j\le n$ and $1\le s\le9$, and let $W\in\mathbb Q[X]$ be arbitrary. From the actual shifted numerator $N_{n,j}$ and erased-factor denominator $D_{n,j}$, define $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}\in\mathbb Q[[z]]$. Set $U_{n,j}(z)=-j(n-j)+(n-2j)z+z^2$, $c_{n,j,\ell}=[z^{9-\ell}]S_{n,j}$ and $c^W_{n,j,s}=[z^{9-s}](S_{n,j}W(U_{n,j}))$. Then
--
--   $$c^W_{n,j,s}=\sum_{\ell=s}^{9}c_{n,j,\ell}[z^{\ell-s}]W\bigl(-j(n-j)+(n-2j)z+z^2\bigr).$$
--
--   Every coefficient is extracted from the genuine formal quotient. The identity covers all nine local orders, all natural $n$ including zero, and all polynomial multipliers including zero. It supplies a local finite convolution; it does not assert a global partial-fraction formula, a full aggregate coefficient map, or its inverse.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-jet-2026-10-03.md (actual shifted numerator, cleared denominator, formal local quotient and all nine convolution orders); underlying missions/zeta9/round5/research/arithmetic.md, equation (5), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMapJet.lean, SHA256 e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a; frozen actual Base source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 191–197.

import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.coefficient_convolution_explicit (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        (W.comp (C (-(j : ℚ) * (n - j : ℕ)) +
          C ((n : ℚ) - 2 * j) * X + X ^ 2)).coeff (l - s):= by sorry
