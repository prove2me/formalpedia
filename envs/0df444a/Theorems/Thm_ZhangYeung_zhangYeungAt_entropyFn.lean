-- Prove2me | Theorems.Thm_ZhangYeung_zhangYeungAt_entropyFn
-- name    : ZhangYeung.zhangYeungAt_entropyFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:20.012097+00:00
-- url     : https://prove2.me/theorems/04dd5a22-01dd-4ba8-9b1b-a5babec6e890
-- title:
--   Zhang Yeung: zhang Yeung At entropy Fn
-- statement:
--   The permutation-indexed bridge: at any permutation `π` of `Fin 4`, the entropy function
--   satisfies
--   the Zhang-Yeung inequality (paper eq. 21) at the labeling `(π 0, π 1, π 2, π 3)`. Proved
--   by
--   unfolding `zhangYeungAt`, rewriting each `entropyFn` evaluation into a joint entropy via
--   the
--   per-subset bridge lemmas, and matching the resulting inequality against M3's
--   `ZhangYeung.zhangYeung` applied to `(X (π 0), X (π 1), X (π 2), X (π 3))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L757-L803
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L757-L803

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

theorem ZhangYeung.zhangYeungAt_entropyFn
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3) := by sorry
