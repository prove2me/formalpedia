-- Prove2me | Theorems.Thm_ZhangYeung_entropyFn_singleton
-- name    : ZhangYeung.entropyFn_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:03.985805+00:00
-- url     : https://prove2.me/theorems/e2dc806a-3ac6-4324-b3d9-1ec038b72151
-- title:
--   Zhang Yeung: entropy Fn singleton
-- statement:
--   Per-subset bridge lemma at a singleton subset: `entropyFn X μ {i} = H[X i; μ]`. The
--   joint tuple
--   over the single-element subset `{i}` is, up to a measurable bijection into `S i`, just
--   `X i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L613-L634
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L613-L634

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
omit [IsProbabilityMeasure μ]

theorem ZhangYeung.entropyFn_singleton (hX : ∀ i, Measurable (X i)) (i : Fin 4) :
    entropyFn X μ {i} = H[X i; μ] := by sorry
