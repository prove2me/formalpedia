-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapNumeratorPartialFractions_actual_numerator_polynomial_partial_fractions
-- name    : ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-07T08:13:12.987098+00:00
-- url     : https://prove2.me/theorems/de4d17b1-b2a9-4eb5-b104-8abe2afd787b
-- title:
--   Actual numerator polynomial partial fractions
-- statement:
--   Let $m$ be a nonnegative integer, and write
--   $$
--   D_m(z)=\prod_{k=0}^{m}(z+k),\qquad
--   C_{m,j}(z)=\prod_{\substack{0\le k\le m\\k\ne j}}(z+k).
--   $$
--   For $0\le j\le m$ and $1\le s\le9$, define the rational coefficient
--   $$
--   c_{m,j,s}(A)=[X^{9-s}]\,
--   \frac{A(X-j)}{C_{m,j}(X-j)^9}
--   $$
--   using the formal power series at $X=0$. The denominator has nonzero constant coefficient, so this formal inverse is defined.
--
--   If $A$ is a rational polynomial satisfying $\deg A<9(m+1)$, then its reconstructed numerator is exactly $A$:
--   $$
--   A(z)=\sum_{j=0}^{m}\sum_{s=1}^{9}
--   c_{m,j,s}(A)\,C_{m,j}(z)^9(z+j)^{9-s}.
--   $$
--   The zero polynomial and $m=0$ are included. This finite polynomial identity is the reconstruction statement behind the rational partial-fraction formula; no existence of a coefficient array is assumed.
--
--   **Formalization Note** The hypothesis uses the natural degree of the rational polynomial. The coefficients are defined by the original formal series, rather than chosen from an abstract decomposition.
-- source:
--   Original zeta9 research, 2026-10-04: research/coefficient-map-numerator-pf-native-2026-10-04.md; formalization/CoefficientMapNumeratorPartialFractions.lean, complete SOURCE SHA256 2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77. Exact theorem: ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions.

import Definitions.Def_ZetaNine_CoefficientMapNumeratorPF

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial ZetaNine ZetaNine.CoefficientMapNumeratorPartialFractions ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) : A = numeratorPartialNumerator m A:= by sorry
