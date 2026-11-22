-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeung_averaged
-- name    : ZhangYeung.zhangYeung_averaged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:01:56.4914+00:00
-- url     : https://prove2.me/theorems/f6a3e7d0-aef6-419a-931a-ae8130bb5821
-- title:
--   Zhang Yeung: zhang Yeung averaged
-- statement:
--   **The averaged symmetric form of Theorem 3** [@zhangyeung1998, §III, eq. 23]:
--
--     `Δ(Z, U | X, Y) ≤ (1/2)·I(X; Y) + (1/4)·(I(X; ⟨Z, U⟩) + I(Y; ⟨Z, U⟩))`.
--
--   The paper highlights this as Theorem 3's headline statement; it follows by averaging
--   eqs. (21) and
--   (22) via the M1 `delta_form23_of_form21_form22` averaging lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L257-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean#L257-L273

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

theorem ZhangYeung.zhangYeung_averaged
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by sorry
