-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapFiniteSum_harmonic_difference_eq_shifted
-- name    : ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:04:54.635342+00:00
-- url     : https://prove2.me/theorems/dc845325-063a-4a97-a4e7-86453335e09a
-- title:
--   Exact finite shifted harmonic difference for every natural order
-- statement:
--   For every natural order $s$, cutoff $T$ and shift $j$, the existing actual finite harmonic numbers obey
--
--   $$H_{T+j}^{(s)}-H_T^{(s)}=\sum_{k=1}^j\frac1{(T+k)^s}.$$
--
--   There is no restriction $s\ge1$: this includes $s=0$, as well as $T=0$ and $j=0$. Empty finite intervals give zero and all terms use the existing rational harmonicPower definition. No properness, coefficient, reflection or convergence hypothesis is required.
-- source:
--   Zeta(9) actual finite harmonic summation: missions/zeta9/research/coefficient-map-finite-sum-2026-10-03.md. Frozen missions/zeta9/formalization/CoefficientMapFiniteSum.lean SHA256 b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97. Coefficients are the actual weighted formal local jets of the p=9,q=1,m=n rational function, using the genuine finite global partial-fraction identity. Original declaration lines 139–142.

import Definitions.Def_ZetaNine_CoefficientMapFiniteSum

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted (s T j : ℕ) :
    harmonicPower s (T + j) - harmonicPower s T =
      ∑ k ∈ Icc 1 j, 1 / ((T : ℚ) + (k : ℚ)) ^ s:= by sorry
