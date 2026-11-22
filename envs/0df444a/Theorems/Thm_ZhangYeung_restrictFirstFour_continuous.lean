-- Prove2me | Theorems.Thm_ZhangYeung_restrictFirstFour_continuous
-- name    : ZhangYeung.restrictFirstFour_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:10.446871+00:00
-- url     : https://prove2.me/theorems/755ef199-0f5b-4878-8ac6-9e08eb836a86
-- title:
--   Zhang Yeung: restrict First Four continuous
-- statement:
--   `restrictFirstFour` is continuous in the pointwise topology.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L138-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L138-L141

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

theorem ZhangYeung.restrictFirstFour_continuous {n : ℕ} (hn : 4 ≤ n) :
  Continuous (restrictFirstFour hn) := by sorry
