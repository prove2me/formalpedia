-- Prove2me | Theorems.Thm_ZhangYeung_restrictFirstFour_mem_almostEntropicRegionN
-- name    : ZhangYeung.restrictFirstFour_mem_almostEntropicRegionN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:39.264279+00:00
-- url     : https://prove2.me/theorems/dc6afc6a-9bda-424c-839d-1ed8b7c61372
-- title:
--   Zhang Yeung: restrict First Four mem almost Entropic Region N
-- statement:
--   Almost-entropic points remain almost entropic after restriction to the first four
--   coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L199-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L199-L205

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology
universe u

theorem ZhangYeung.restrictFirstFour_mem_almostEntropicRegionN
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ almostEntropicRegionN.{u} n) :
    restrictFirstFour hn F ∈ almostEntropicRegionN.{u} 4 := by sorry
