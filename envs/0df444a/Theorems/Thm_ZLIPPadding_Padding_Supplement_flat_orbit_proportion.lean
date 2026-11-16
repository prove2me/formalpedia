-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_flat_orbit_proportion
-- name    : ZLIPPadding.Padding.Supplement.flat_orbit_proportion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:25:39.006885+00:00
-- url     : https://prove2.me/theorems/1adc02ee-2910-4827-8a1e-c07e7e544c10
-- title:
--   Theorem 6.1 — Flat-orbit proportions including the asymptotic limit
-- statement:
--   For integers $1\le m\le n/2$, let $F_m$ be the flat vectors of $S_m(\mathbb Z^n)$ and set $\eta_{n,m}=4m^4/(31(n-m+1)^3)$. Then
--
--   $$\frac{|F_m|}{|S_m(\mathbb Z^n)|}\ge e^{-\eta_{n,m}},\qquad\frac{|S_m(\mathbb Z^n)\setminus F_m|}{|S_m(\mathbb Z^n)|}\le\eta_{n,m}.$$
--
--   For every sequence of positive integers $m(n)=o(n^{3/4})$, the flat proportion tends to one. Also, for every $n\ge256$ and $1\le m\le n^{3/4}$ the flat proportion is strictly greater than $2/3$. This companion theorem retains both finite inequalities, the complete sequential little-o assertion, and the strict finite-range bound. It provides the flat-mass hypothesis for short-shell recovery.
--
--   Differences from the source:
--   - encoding: m=o(n^(3/4)) and finite cardinality ratios → Tendsto for every positive integer sequence and Finset cardinalities coerced to real numbers; reason: this states the full sequential little-o consequence and preserves both finite inequalities
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 24 (PDF p. 25), Theorem 6.1

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem flat_orbit_proportion :
    (∀ n m : ℕ, 1 ≤ m → 2*m ≤ n →
      flatRatio n m ≥ Real.exp (-flatError n m) ∧
      (((shell n m) \ flat n m).card : ℝ)/(shell n m).card ≤ flatError n m) ∧
    (∀ ms : ℕ → ℕ, (∀ n, 1 ≤ ms n) →
      Filter.Tendsto (fun n => (ms n : ℝ)/(n : ℝ)^(3/4 : ℝ))
        Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => flatRatio n (ms n)) Filter.atTop (nhds 1)) ∧
    (∀ n m : ℕ, shortRange n m → flatRatio n m > 2/3) := by sorry

end ZLIPPadding.Padding.Supplement
