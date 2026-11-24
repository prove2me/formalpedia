-- Prove2me | Theorems.Thm_ZeroCount_mid_band_count
-- name    : ZeroCount.mid_band_count
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:41:37.49881+00:00
-- url     : https://prove2.me/theorems/05ec190b-1dee-4f9b-a303-75546afbd140
-- title:
--   Zeros of zeta with 121 <= Im <= 65000 number at most 85250 with multiplicity
-- statement:
--   For every finite set $U$ of zeros $\rho$ of the Riemann zeta function in the critical strip $0<\Re\rho<1$ with $121\le \Im\rho\le 65000$,
--   $$\sum_{\rho\in U}\operatorname{ord}_{\rho}\zeta \le 85250.$$
--   This is the Turing-method count of the band $[121,65000]$ (with multiplicity), and gives the upper half of the bound $N(T)\le 85288$ for zeros up to height 65000.
-- source:
--   Broughan RH collection, Schoenfeld zero-count lemma (zerocount lane)

import Mathlib

theorem ZeroCount.mid_band_count (U : Finset ℂ)
    (hU : ∀ ρ ∈ U, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ (121 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 65000) :
    ∑ ρ ∈ U, analyticOrderNatAt riemannZeta ρ ≤ 85250 := by sorry
