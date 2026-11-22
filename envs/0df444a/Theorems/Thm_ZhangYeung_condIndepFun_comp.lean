-- Prove2me | Theorems.Thm_ZhangYeung_condIndepFun_comp
-- name    : ZhangYeung.condIndepFun_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:52:26.310958+00:00
-- url     : https://prove2.me/theorems/c69d7e46-f46c-4f9a-a461-ecb3f81583ff
-- title:
--   Zhang Yeung: cond Indep Fun comp
-- statement:
--   Post-composition of a `CondIndepFun` statement on its two measured coordinates by
--   independent
--   measurable functions `φ` and `ψ`. The conditioner `k` is unchanged. Mathlib's
--   `CondIndepFun.comp`
--   uses the σ-algebra form of conditional independence and does not apply to PFR's
--   random-variable
--   form; this lemma fills that gap by unfolding through `condIndepFun_iff` to a fibrewise
--   `∀ᵐ`-family
--   of `IndepFun` statements, applying Mathlib's `IndepFun.comp` inside each fibre, and
--   repackaging.
--   Promoted from `ZhangYeung/CopyLemma.lean` as of M3 (the second consumer).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L145-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Prelude.lean#L145-L155

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung

theorem ZhangYeung.condIndepFun_comp
    {Ω α α' β β' γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β'] [MeasurableSpace γ]
    {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    {φ : α → α'} {ψ : β → β'}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : CondIndepFun f g k μ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) k μ := by sorry
