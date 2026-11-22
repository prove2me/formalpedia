-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeung_dual
-- name    : ZhangYeung.zhangYeung_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:56:36.155863+00:00
-- url     : https://prove2.me/theorems/06398482-4e5b-4826-a9fe-cb1986f292ac
-- title:
--   Zhang Yeung: zhang Yeung dual
-- statement:
--   **The `X ↔ Y` dual of Theorem 3** [@zhangyeung1998, §III, eq. 22]:
--
--     `Δ(Z, U | X, Y) ≤ (1/2)·(I(X; Y) + I(Y; ⟨Z, U⟩) - I(Z; U | X) + I(Z; U | Y))`.
--
--   Obtained from `zhangYeung` by swapping `X` and `Y` in the hypotheses, using
--   `delta_comm_cond` to
--   rewrite the left-hand side back to the original delta, and `mutualInfo_comm` to rewrite
--   `I[Y : X]`
--   as `I[X : Y]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L238-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L238-L248

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]

theorem ZhangYeung.zhangYeung_dual
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ]) := by sorry
