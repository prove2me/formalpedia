-- Prove2me | Theorems.Thm_ZhangYeung_restrictFirstFour_mem_entropyRegionN
-- name    : ZhangYeung.restrictFirstFour_mem_entropyRegionN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:33.174401+00:00
-- url     : https://prove2.me/theorems/9a42aba0-d50b-4f63-86aa-57171d193e16
-- title:
--   Zhang Yeung: restrict First Four mem entropy Region N
-- statement:
--   Entropic points remain entropic after restriction to the first four coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L179-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/EntropyRegion.lean#L179-L193

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

theorem ZhangYeung.restrictFirstFour_mem_entropyRegionN
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ entropyRegionN.{u} n) :
    restrictFirstFour hn F ∈ entropyRegionN.{u} 4 := by sorry
