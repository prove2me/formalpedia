-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapNumeratorPartialFractions_actual_numerator_global_partial_fractions
-- name    : ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-07T08:13:02.96477+00:00
-- url     : https://prove2.me/theorems/080d88e9-11af-45ae-96cf-4b2bb0041690
-- title:
--   Actual numerator global partial fractions
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
--   Suppose that $A$ is a rational polynomial with $\deg A<9(m+1)$. At every rational $t$ satisfying $t+k\ne0$ for all $0\le k\le m$,
--   $$
--   \frac{A(t)}{D_m(t)^9}
--   =\sum_{j=0}^{m}\sum_{s=1}^{9}
--   \frac{c_{m,j,s}(A)}{(t+j)^s}.
--   $$
--   This is the complete finite partial-fraction expansion with the actual local coefficients. The regular-point condition explicitly excludes all poles, so no cancellation at a zero denominator is asserted. The case $m=0$ is included.
-- source:
--   Original zeta9 research, 2026-10-04: research/coefficient-map-numerator-pf-native-2026-10-04.md; formalization/CoefficientMapNumeratorPartialFractions.lean, complete SOURCE SHA256 2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77. Exact theorem: ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions.

import Definitions.Def_ZetaNine_CoefficientMapNumeratorPF

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial ZetaNine ZetaNine.CoefficientMapNumeratorPartialFractions ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s:= by sorry
