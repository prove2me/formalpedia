-- Prove2me | Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness_n
-- name    : ZhangYeung.not_zhangYeungHolds_witness_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:51.824772+00:00
-- url     : https://prove2.me/theorems/2ddf0fa5-3715-4476-89af-aedea0c78af2
-- title:
--   Zhang Yeung: not zhang Yeung Holds witness n
-- statement:
--   Part (b) lifted to `Fin n`: the lifted witness fails `zhangYeungHoldsN` at the lifted
--   canonical
--   labeling.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1128-L1137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1128-L1137

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

theorem ZhangYeung.not_zhangYeungHolds_witness_n {n : ℕ} (hn : 4 ≤ n) :
    ¬ zhangYeungHoldsN (FWitnessN hn) := by sorry
