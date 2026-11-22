-- Prove2me | Theorems.Thm_ZhangYeungImport_MeasureTheory_lintegral_eq_zero_of_ae_zero
-- name    : ZhangYeungImport.MeasureTheory.lintegral_eq_zero_of_ae_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:26.033411+00:00
-- url     : https://prove2.me/theorems/e57ccf15-f56e-4391-91f7-2e912ccb3fb4
-- title:
--   Measure Theory: lintegral eq zero of ae zero
-- statement:
--   The Measure Theory construction uses the lintegral eq zero of ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L24-L29
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L24-L29

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

theorem ZhangYeungImport.MeasureTheory.lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s,
  f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by sorry

alias «MeasureTheory».«lintegral_eq_zero_of_ae_zero» := ZhangYeungImport.MeasureTheory.lintegral_eq_zero_of_ae_zero
