-- Prove2me | Theorems.Thm_ZhangYeung_copyLemma
-- name    : ZhangYeung.copyLemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:53:43.123526+00:00
-- url     : https://prove2.me/theorems/47461522-ca05-4046-acc9-bd2c0ece4ac0
-- title:
--   Zhang Yeung: copy Lemma
-- statement:
--   **The Zhang-Yeung copy lemma** [@zhangyeung1998, §III, eq. 44]. Given four discrete
--   random
--   variables `X, Y, Z, U` on a probability space `(Ω, μ)`, there exists an extended
--   probability space
--   `(Ω', ν)` carrying six projected random variables `X', Y', X₁, Y₁, Z', U'` such that
--   `(X', Y', Z',
--   U')` and `(X₁, Y₁, Z', U')` each have the original joint law of `(X, Y, Z, U)` under
--   `μ`, and the
--   two pairs `(X', Y')` and `(X₁, Y₁)` are conditionally independent given the shared pair
--   `(Z', U')`.
--   This is a direct wrapper around `ProbabilityTheory.condIndep_copies` applied to `⟨X, Y⟩`
--   conditioned on `⟨Z, U⟩`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L143-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/CopyLemma.lean#L143-L182

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u

theorem ZhangYeung.copyLemma
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [Finite S₃] [Finite S₄]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν := by sorry
