-- Prove2me | Theorems.Thm_ZhangYeung_entropyFn_pair
-- name    : ZhangYeung.entropyFn_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:13.153489+00:00
-- url     : https://prove2.me/theorems/d1c60712-fd79-4d28-8d47-c7154854d2cc
-- title:
--   Zhang Yeung: entropy Fn pair
-- statement:
--   Per-subset bridge lemma at a two-element subset: `entropyFn X μ {i, j} = H[⟨X i, X j⟩;
--   μ]` for `i ≠
--   j`. The joint tuple over `{i, j}` is measurably bijective with the pair `(X i, X j)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L642-L667
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L642-L667

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

theorem ZhangYeung.entropyFn_pair (hX : ∀ i, Measurable (X i))
    {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩; μ] := by sorry
