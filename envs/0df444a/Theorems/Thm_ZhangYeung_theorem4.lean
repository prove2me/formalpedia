-- Prove2me | Theorems.Thm_ZhangYeung_theorem4
-- name    : ZhangYeung.theorem4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:28.931632+00:00
-- url     : https://prove2.me/theorems/ac60c189-694f-4cce-90fa-20c06051273a
-- title:
--   Zhang Yeung: theorem4
-- statement:
--   **Theorem 4 of [@zhangyeung1998, §II, eq. 26]** at `n = 4`. The Shannon outer bound
--   `Γ_4` strictly
--   contains the closure of the entropic region: there exists a set function in `Γ_4` that
--   is not
--   almost entropic. The non-membership claim is universe-polymorphic: for every universe
--   `u`,
--   `FWitness ∉ almostEntropicRegionN.{u} 4`, since the closedness argument in
--   `zhangYeungRegion_4`
--   lives entirely at the level of `Finset (Fin 4) → ℝ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1011-L1014
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1011-L1014

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

theorem ZhangYeung.theorem4 :
    ∃ F : Finset (Fin 4) → ℝ,
      F ∈ shannonRegionN 4 ∧ F ∉ almostEntropicRegionN.{u} 4 := by sorry
