-- Prove2me | Theorems.Thm_ZhangYeung_entropyFn_empty
-- name    : ZhangYeung.entropyFn_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:08:40.846027+00:00
-- url     : https://prove2.me/theorems/5b7c4b8d-d05f-48fc-bbb6-e161aa5200e0
-- title:
--   Zhang Yeung: entropy Fn empty
-- statement:
--   Per-subset bridge lemma at the empty subset: `entropyFn X μ ∅ = 0`. The subtype `{j // j
--   ∈ (∅ :
--   Finset (Fin 4))}` is empty, so the dependent-product codomain `∀ j : ∅, S j.1` is a
--   subsingleton;
--   the joint tuple is constant, and its entropy is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L594-L604
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L594-L604

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
omit [∀ i, Finite (S i)]

theorem ZhangYeung.entropyFn_empty : entropyFn X μ ∅ = 0 := by sorry
