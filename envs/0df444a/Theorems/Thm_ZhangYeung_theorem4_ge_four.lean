-- Prove2me | Theorems.Thm_ZhangYeung_theorem4_ge_four
-- name    : ZhangYeung.theorem4_ge_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:47.02381+00:00
-- url     : https://prove2.me/theorems/8a91802a-07a8-47be-a8fe-8fb542fd8876
-- title:
--   Zhang Yeung: theorem4 ge four
-- statement:
--   **Theorem 4 of [@zhangyeung1998, §II, eq. 26]** for all `n ≥ 4`. The Shannon outer bound
--   `Γ_n`
--   strictly contains the closure of the entropic region: there exists a set function in
--   `Γ_n` that is
--   not almost entropic. The non-membership claim is universe-polymorphic: for every
--   universe `u`,
--   `FWitnessN hn ∉ almostEntropicRegionN.{u} n`, by restricting any hypothetical
--   almost-entropic
--   realization back down to the first four coordinates and applying the `n = 4` exclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1161-L1169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1161-L1169

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u

theorem ZhangYeung.theorem4_ge_four (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ,
      F ∈ shannonRegionN n ∧ F ∉ almostEntropicRegionN.{u} n := by sorry
