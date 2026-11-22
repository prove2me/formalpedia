-- Prove2me | Theorems.Thm_ZhangYeung_delta_le_mutualInfo
-- name    : ZhangYeung.delta_le_mutualInfo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:07.268471+00:00
-- url     : https://prove2.me/theorems/ff64836b-0137-415a-8c92-50c84ce8cfea
-- title:
--   Zhang Yeung: delta le mutual Info
-- statement:
--   `Δ(Z, U | X, Y) ≤ I(Z; U)`: the delta is bounded above by the unconditional mutual
--   information,
--   since conditional mutual information is non-negative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L236-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L236-L242

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
variable [Finite S₁] [Finite S₂]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]

theorem ZhangYeung.delta_le_mutualInfo
    {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    {X : Ω → S₃} {Y : Ω → S₄} (μ : Measure Ω) :
    delta Z U X Y μ ≤ I[Z : U; μ] := by sorry
