-- Prove2me | Theorems.Thm_ZhangYeung_delta_def
-- name    : ZhangYeung.delta_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:51:55.731259+00:00
-- url     : https://prove2.me/theorems/f588a631-2021-45fa-9e42-8bbc2fe353a1
-- title:
--   Zhang Yeung: delta def
-- statement:
--   Definitional unfolding of `delta`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L123-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L123-L126

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

theorem ZhangYeung.delta_def (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω
  → S₄) (μ : Measure Ω) :
    delta Z U X Y μ
      = I[Z : U; μ] - I[Z : U | X; μ] - I[Z : U | Y; μ] := by sorry
