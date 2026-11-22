-- Prove2me | Theorems.Thm_ZhangYeung_entropyFn_triple
-- name    : ZhangYeung.entropyFn_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:08.193669+00:00
-- url     : https://prove2.me/theorems/56f19c05-e5cf-4ce0-a8d8-7f69e64f3306
-- title:
--   Zhang Yeung: entropy Fn triple
-- statement:
--   Per-subset bridge lemma at a three-element subset: `entropyFn X μ {i, j, k} = H[⟨X i, ⟨X
--   j, X k⟩⟩;
--   μ]` for pairwise distinct `i, j, k`. The joint tuple over `{i, j, k}` is measurably
--   bijective with
--   the triple `(X i, (X j, X k))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L677-L703
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L677-L703

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

theorem ZhangYeung.entropyFn_triple (hX : ∀ i, Measurable (X i))
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    entropyFn X μ {i, j, k} = H[⟨X i, ⟨X j, X k⟩⟩; μ] := by sorry
