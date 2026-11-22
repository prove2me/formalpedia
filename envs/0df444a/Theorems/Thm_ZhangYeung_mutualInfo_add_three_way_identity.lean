-- Prove2me | Theorems.Thm_ZhangYeung_mutualInfo_add_three_way_identity
-- name    : ZhangYeung.mutualInfo_add_three_way_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:32.919588+00:00
-- url     : https://prove2.me/theorems/56b231e0-4a3c-473a-9a73-67aa181323b8
-- title:
--   Zhang Yeung: mutual Info add three way identity
-- statement:
--   The three-way interaction identity
--
--     `I[X : Y] + I[X : Z] = I[X : ⟨Y, Z⟩] + I[Y : Z] - I[Y : Z | X]`.
--
--   Equivalent to a pair of chain-rule applications on `I[X : ⟨Y, Z⟩]`, together with the
--   defining
--   identity `I[Y : Z | X] = I[Y : Z] - I[X : Y : Z]` for the three-way interaction
--   information.
--   Promoted from `ZhangYeung/Theorem3.lean` as of M5.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L86-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L86-L101

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung

theorem ZhangYeung.mutualInfo_add_three_way_identity
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y; μ] + I[X : Z; μ]
      = I[X : ⟨Y, Z⟩; μ] + I[Y : Z; μ] - I[Y : Z | X; μ] := by sorry
