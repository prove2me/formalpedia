-- Prove2me | Theorems.Thm_ZhangYeung_entropyFn_quad
-- name    : ZhangYeung.entropyFn_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:09:38.55181+00:00
-- url     : https://prove2.me/theorems/794eae5f-c689-4a78-abad-4f565a3bbf43
-- title:
--   Zhang Yeung: entropy Fn quad
-- statement:
--   Per-subset bridge lemma at the full four-element subset: `entropyFn X μ {0, 1, 2, 3} =
--   H[⟨X 0, ⟨X
--   1, ⟨X 2, X 3⟩⟩⟩; μ]`. The joint tuple over the full index set is measurably bijective
--   with the
--   right-associated 4-tuple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L713-L743
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L713-L743

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

theorem ZhangYeung.entropyFn_quad (hX : ∀ i, Measurable (X i)) :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩; μ] := by sorry
