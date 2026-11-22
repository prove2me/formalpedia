-- Prove2me | Theorems.Thm_pac_lower_bound
-- name    : pac_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:56.393962+00:00
-- url     : https://prove2.me/theorems/ff315787-bb62-414c-8055-4edaf46d44c8
-- title:
--   pac lower bound: pac lower bound
-- statement:
--   PAC lower bound: sample complexity is at least linear in d/ε.
--
--       This statement asserts the specific quantitative lower bound from learning
--       theory:
--         m ≥ ⌈(d-1)/(64ε)⌉ for PAC learning with VCDim = d.
--       Note: the tight constant is (d-1)/(2ε) (EHKV 1989); see EHKV.lean.
--
--       Proof route: construct 2^d labelings on a shattered set of size d,
--       use double-averaging + reversed Markov to show that m < (d-1)/(64ε)
--       implies Pr[error ≤ ε] < 6 / 7 under uniform distribution on shattered set.
--
--       KU₂₀: The exact constant (1 / 7 vs 1 / 8 vs 1 / 4) depends on the proof technique.
--       The factor (d-1) vs d also varies by source.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L163-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L163-L176

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem pac_lower_bound (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d)
    [MeasurableConceptClass X C] :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ := by sorry
