-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeungHolds_of_entropy
-- name    : ZhangYeung.zhangYeungHolds_of_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:23.361548+00:00
-- url     : https://prove2.me/theorems/227286a2-d5de-4a1d-a598-963b164f9e57
-- title:
--   Zhang Yeung: zhang Yeung Holds of entropy
-- statement:
--   Part (c), the full bridge: the entropy function of any four-variable random-variable
--   family lies in
--   `tildeΓ_4`. One-line wrapper around `zhangYeungAt_entropyFn`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L810-L818
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L810-L818

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

theorem ZhangYeung.zhangYeungHolds_of_entropy
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    zhangYeungHolds (entropyFn X μ) := by sorry
