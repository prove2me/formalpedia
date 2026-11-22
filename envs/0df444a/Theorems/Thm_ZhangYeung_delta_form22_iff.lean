-- Prove2me | Theorems.Thm_ZhangYeung_delta_form22_iff
-- name    : ZhangYeung.delta_form22_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:30.019511+00:00
-- url     : https://prove2.me/theorems/21967f64-95f5-4a14-a332-286c0250fb0d
-- title:
--   Zhang Yeung: delta form22 iff
-- statement:
--   Paper eq. (22) of [@zhangyeung1998, §III]: the `X ↔ Y` swap of `delta_form21_iff`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L157-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L157-L163

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]

theorem ZhangYeung.delta_form22_iff
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ] - I[Z : U | X; μ] + I[Z : U | Y; μ]
      ↔ 2 * I[Z : U; μ] - I[Z : U | X; μ] - 3 * I[Z : U | Y; μ]
          ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ] := by sorry
