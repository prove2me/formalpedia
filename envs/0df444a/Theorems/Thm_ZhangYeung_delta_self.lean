-- Prove2me | Theorems.Thm_ZhangYeung_delta_self
-- name    : ZhangYeung.delta_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:28.611039+00:00
-- url     : https://prove2.me/theorems/302f2fff-f48a-438a-bf3c-7cf69f9efdd3
-- title:
--   Zhang Yeung: delta self
-- statement:
--   The case `X = Y`: `Δ(Z, U | X, X) = I(Z; U) - 2·I(Z; U | X)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L135-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L135-L137

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

theorem ZhangYeung.delta_self (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (μ : Measure Ω) :
    delta Z U X X μ = I[Z : U; μ] - 2 * I[Z : U | X; μ] := by sorry
