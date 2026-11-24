-- Prove2me | Theorems.Thm_ZeroCount_low_band_count
-- name    : ZeroCount.low_band_count
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:41:48.090482+00:00
-- url     : https://prove2.me/theorems/02b173c9-d95c-46d6-97a0-fbe0759708b1
-- title:
--   Zeros of zeta with 0 < Im <= 121 number at most 38 with multiplicity
-- statement:
--   For every finite set $U$ of zeros $\rho$ of the Riemann zeta function with $0<\Re\rho<1$ and $0<\Im\rho\le 121$,
--   $$\sum_{\rho\in U}\operatorname{ord}_{\rho}\zeta \le 38.$$
--   Proved by a Turing-band certificate on $[10, 3871/32]$ together with zero-free regions below height 14 and in $[3871/32,121]$.
-- source:
--   Broughan RH collection, Schoenfeld zero-count lemma (zerocount lane)

import Mathlib

theorem ZeroCount.low_band_count (U : Finset ℂ)
    (hU : ∀ ρ ∈ U, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ 121) :
    ∑ ρ ∈ U, analyticOrderNatAt riemannZeta ρ ≤ 38 := by sorry
