-- Prove2me | Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness
-- name    : ZhangYeung.not_zhangYeungHolds_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:24.316795+00:00
-- url     : https://prove2.me/theorems/07d4b5c4-eb0c-41c9-a1b3-b837be786641
-- title:
--   Zhang Yeung: not zhang Yeung Holds witness
-- statement:
--   Part (b) of Theorem 4: the witness fails the Zhang-Yeung inequality at the canonical
--   labeling `(i,
--   j, k, l) = (2, 3, 0, 1)` (paper lines 378-388). The permutation exhibiting the violation
--   is `σ =
--   Equiv.swap 0 2 * Equiv.swap 1 3`; after permutation evaluation the obligation is the
--   canonical
--   failure `not_zhangYeungAt_witness_canonical`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L553-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L553-L560

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

theorem ZhangYeung.not_zhangYeungHolds_witness : ¬ zhangYeungHolds FWitness := by sorry
