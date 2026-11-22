-- Prove2me | Theorems.Thm_ZhangYeung_delta_eq_entropy
-- name    : ZhangYeung.delta_eq_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:55:55.147149+00:00
-- url     : https://prove2.me/theorems/25491f9b-0586-4471-a967-2ef5db1450d3
-- title:
--   Zhang Yeung: delta eq entropy
-- statement:
--   Expand `delta` all the way down to raw entropy terms, using `mutualInfo_def` and
--   `condMutualInfo_eq`. This is the bridge to any reasoning at the entropy layer directly
--   (for
--   example, evaluating `delta` on a concrete four-variable distribution when checking
--   bounds or
--   building counterexamples).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L257-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Delta.lean#L257-L265

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
variable [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

theorem ZhangYeung.delta_eq_entropy
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = (H[Z; μ] + H[U; μ] - H[⟨Z, U⟩; μ])
        - (H[Z | X; μ] + H[U | X; μ] - H[⟨Z, U⟩ | X; μ])
        - (H[Z | Y; μ] + H[U | Y; μ] - H[⟨Z, U⟩ | Y; μ]) := by sorry
