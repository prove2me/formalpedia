-- Prove2me | Theorems.Thm_ZhangYeung_theorem4_finite
-- name    : ZhangYeung.theorem4_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:02:32.754794+00:00
-- url     : https://prove2.me/theorems/ac10deee-84fd-4358-8a0a-9d4778f4242c
-- title:
--   Zhang Yeung: theorem4 finite
-- statement:
--   Finite auxiliary form of Theorem 4 at `n = 4`: the witness lies in `Γ_4` but is not the
--   entropy
--   function of any single four-variable discrete family. The exact paper-level closure
--   statement is
--   the later theorem `theorem4`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L829-L842
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L829-L842

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

theorem ZhangYeung.theorem4_finite :
    ∃ F : Finset (Fin 4) → ℝ,
      shannonCone F ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {S : Fin 4 → Type u}
        [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
        [∀ i, MeasurableSingletonClass (S i)]
        (X : ∀ i : Fin 4, Ω → S i) (_ : ∀ i, Measurable (X i)),
        F ≠ entropyFn X μ := by sorry
