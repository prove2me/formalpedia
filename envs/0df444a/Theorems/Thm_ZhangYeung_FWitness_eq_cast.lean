-- Prove2me | Theorems.Thm_ZhangYeung_FWitness_eq_cast
-- name    : ZhangYeung.FWitness_eq_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:54:20.457428+00:00
-- url     : https://prove2.me/theorems/8f896b5d-27fe-46c7-8e13-f594a4224f07
-- title:
--   Zhang Yeung: FWitness eq cast
-- statement:
--   Definitional-shape lemma: `FWitness` is the pointwise `ℚ → ℝ` cast of `FWitnessℚ`.
--   Used to push
--   `FWitness` into `FWitnessℚ`-shaped goals before closing them over `ℚ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L274-L275
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem4.lean#L274-L275

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

theorem ZhangYeung.FWitness_eq_cast (S : Finset (Fin 4)) :
    FWitness S = (FWitnessℚ S : ℝ) := by sorry
