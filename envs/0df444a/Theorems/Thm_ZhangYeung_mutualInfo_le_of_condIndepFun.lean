-- Prove2me | Theorems.Thm_ZhangYeung_mutualInfo_le_of_condIndepFun
-- name    : ZhangYeung.mutualInfo_le_of_condIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:41.242089+00:00
-- url     : https://prove2.me/theorems/167101b8-8325-4ec3-b2a0-890b59bafb3a
-- title:
--   Zhang Yeung: mutual Info le of cond Indep Fun
-- statement:
--   Data processing for PFR's random-variable form of `CondIndepFun`: if `X` and `Y` are
--   conditionally
--   independent given `Z`, then `I[X : Y] ≤ I[X : Z]`. Promoted from
--   `ZhangYeung/Theorem3.lean` as of
--   M5.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L110-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L110-L130

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung

theorem ZhangYeung.mutualInfo_le_of_condIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : CondIndepFun X Y Z μ) :
    I[X : Y; μ] ≤ I[X : Z; μ] := by sorry
