-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapJet_integer_coefficient_convolution
-- name    : ZetaNine.CoefficientMapJet.integer_coefficient_convolution
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T16:07:09.652719+00:00
-- url     : https://prove2.me/theorems/3b41126b-9a8a-409c-bd06-e840790f686b
-- title:
--   Actual local convolution with integer polynomial multipliers
-- statement:
--   Let $n,j,s$ be natural numbers with $j\le n$ and $1\le s\le9$, and let $W\in\mathbb Z[X]$ be arbitrary. Put $U^{\mathbb Z}_{n,j}(z)=-j(n-j)+(n-2j)z+z^2\in\mathbb Z[z]$, and let $\overline W\in\mathbb Q[X]$ be the coefficientwise image of $W$. Define the actual formal quotient $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}$ from the shifted finite products and set $c_{n,j,\ell}=[z^{9-\ell}]S_{n,j}$, $c^{\overline W}_{n,j,s}=[z^{9-s}](S_{n,j}\overline W(U_{n,j}))$. Then
--
--   $$c^{\overline W}_{n,j,s}=\sum_{\ell=s}^{9}c_{n,j,\ell}\,\iota\!\left([z^{\ell-s}]W(U^{\mathbb Z}_{n,j}(z))\right),$$
--
--   where $\iota:\mathbb Z\to\mathbb Q$ is the natural inclusion. The multiplier coefficients inside $\iota$ are integers, while the actual local coefficients $c_{n,j,\ell}$ remain rational and need not be integers. This applies in particular to integer quartic multipliers. Arbitrary-degree local validity does not imply the degree constraints or convergence needed for an infinite-sum application.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-jet-2026-10-03.md (actual shifted numerator, cleared denominator, formal local quotient and all nine convolution orders); underlying missions/zeta9/round5/research/arithmetic.md, equation (5), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMapJet.lean, SHA256 e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a; frozen actual Base source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 199–208.

import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.integer_coefficient_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ):= by sorry
