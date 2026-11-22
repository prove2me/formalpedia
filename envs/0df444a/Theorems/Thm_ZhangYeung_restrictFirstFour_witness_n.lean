-- Prove2me | Theorems.Thm_ZhangYeung_restrictFirstFour_witness_n
-- name    : ZhangYeung.restrictFirstFour_witness_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:51.780661+00:00
-- url     : https://prove2.me/theorems/1fbd764c-70dd-457a-bb81-0f626f42ef8f
-- title:
--   Zhang Yeung: restrict First Four witness n
-- statement:
--   Restricting the lifted witness back to the first four coordinates recovers the base
--   witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1102-L1107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L1102-L1107

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

theorem ZhangYeung.restrictFirstFour_witness_n {n : ℕ} (hn : 4 ≤ n) :
    restrictFirstFour hn (FWitnessN hn) = FWitness := by sorry
