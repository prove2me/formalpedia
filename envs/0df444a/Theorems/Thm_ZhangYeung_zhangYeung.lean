-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeung
-- name    : ZhangYeung.zhangYeung
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:04.296884+00:00
-- url     : https://prove2.me/theorems/a2dc46b5-56e0-4545-89cf-843d6f9bd524
-- title:
--   Zhang Yeung: zhang Yeung
-- statement:
--   **Theorem 3 of [@zhangyeung1998, §III, eq. 21]** -- the Zhang-Yeung inequality in
--   the
--   asymmetric form the copy-lemma proof naturally produces:
--
--     `Δ(Z, U | X, Y) ≤ (1/2)·(I(X; Y) + I(X; ⟨Z, U⟩) + I(Z; U | X) - I(Z; U | Y))`.
--
--   This is the first known non-Shannon-type information inequality, in the form paper eq.
--   (21) states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L218-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L218-L227

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

theorem ZhangYeung.zhangYeung
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * (I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ]) := by sorry
