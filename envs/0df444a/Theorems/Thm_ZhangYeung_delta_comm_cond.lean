-- Prove2me | Theorems.Thm_ZhangYeung_delta_comm_cond
-- name    : ZhangYeung.delta_comm_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:00:40.474875+00:00
-- url     : https://prove2.me/theorems/9a96594b-ba82-411b-a5ba-5becd7780cf7
-- title:
--   Zhang Yeung: delta comm cond
-- statement:
--   Swapping the two conditioning arguments leaves `delta` unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L129-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L129-L132

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

theorem ZhangYeung.delta_comm_cond (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω
  → S₄) (μ : Measure Ω) :
    delta Z U X Y μ = delta Z U Y X μ := by sorry
