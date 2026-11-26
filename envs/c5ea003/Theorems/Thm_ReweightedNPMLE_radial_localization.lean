-- Prove2me | Theorems.Thm_ReweightedNPMLE_radial_localization
-- name    : ReweightedNPMLE.radial_localization
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:20.155919+00:00
-- url     : https://prove2.me/theorems/11e35a6f-b12a-5ba9-b9ce-55bbc698ae54
-- title:
--   Radial localization with ordinary-likelihood and fitted-log bounds
-- statement:
--   Let $U\subset\mathbb R^n$ be convex with $0\in U$, and let $u\in U$ satisfy $1+u_i>0$. Suppose $|w_i-1|\le1/16$ for every coordinate $i$, $A\le1/384$, $E\le1/6144$, and $0\le\tau<1/3072$. Assume, for every $z\in U$, $\sum_i z_i\le0$ and $\langle w-\mathbf1,z\rangle\le A\|z\|_2+E$, and suppose $\sum_iw_i\log(1+u_i)\ge-\tau$. Assume additionally $E\ge0$. Then $$\|u\|_2<1/16,\quad\|u\|_2^2\le36A^2+12E+12\tau,$$ $$0\le-\sum_i\log(1+u_i)\le37A^2+13E+13\tau,$$ $$\sum_i[\log(1+u_i)]^2\le72A^2+24E+24\tau,$$ and $\sum_i(w_i-1)\log(1+u_i)\le37A^2+13E+12\tau$. All sums are unnormalized. These bounds quantify fit robustness for near-optimal weighted likelihoods.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/RadialLocalization.lean#L224-L316

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open scoped BigOperators
open Set

theorem ReweightedNPMLE.radial_localization {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E τ : ℝ) (hE0 : 0 ≤ E) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ ∧
      0 ≤ -(∑ i, Real.log (1 + u i)) ∧
      -(∑ i, Real.log (1 + u i)) ≤
        37 * A ^ 2 + 13 * E + 13 * τ ∧
      ∑ i, Real.log (1 + u i) ^ 2 ≤
        72 * A ^ 2 + 24 * E + 24 * τ ∧
      ∑ i, (w i - 1) * Real.log (1 + u i) ≤
        37 * A ^ 2 + 13 * E + 12 * τ := by sorry
