-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapNumeratorPartialFractions_actual_numerator_local_coefficients_injective
-- name    : ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-07T08:13:09.317984+00:00
-- url     : https://prove2.me/theorems/6401d566-08e7-4206-92c5-b306fe0e5468
-- title:
--   Actual numerator injective partial fractions
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
--   Let $A$ and $B$ be rational polynomials, both of degree below $9(m+1)$. If
--   $$
--   c_{m,j,s}(A)=c_{m,j,s}(B)
--   \quad\text{for every }0\le j\le m\text{ and }1\le s\le9,
--   $$
--   then
--   $$
--   A=B.
--   $$
--   Thus the full array of the actual local coefficients determines a proper numerator uniquely. The assertion covers every nonnegative $m$; it does not assert injectivity of a smaller selection of coefficients.
-- source:
--   Original zeta9 research, 2026-10-04: research/coefficient-map-numerator-pf-native-2026-10-04.md; formalization/CoefficientMapNumeratorPartialFractions.lean, complete SOURCE SHA256 2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77. Exact theorem: ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective.

import Definitions.Def_ZetaNine_CoefficientMapNumeratorPF

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial ZetaNine ZetaNine.CoefficientMapNumeratorPartialFractions ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (heq : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B:= by sorry
