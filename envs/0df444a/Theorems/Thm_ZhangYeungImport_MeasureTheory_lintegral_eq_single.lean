-- Prove2me | Theorems.Thm_ZhangYeungImport_MeasureTheory_lintegral_eq_single
-- name    : ZhangYeungImport.MeasureTheory.lintegral_eq_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:30.870843+00:00
-- url     : https://prove2.me/theorems/c7fc7793-28d7-4777-af63-962e9e5158fa
-- title:
--   Measure Theory: lintegral eq single
-- statement:
--   The Measure Theory construction uses the lintegral eq single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L41-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L41-L47

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]

theorem ZhangYeungImport.MeasureTheory.lintegral_eq_single (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a,
  f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by sorry

alias «MeasureTheory».«lintegral_eq_single» := ZhangYeungImport.MeasureTheory.lintegral_eq_single
