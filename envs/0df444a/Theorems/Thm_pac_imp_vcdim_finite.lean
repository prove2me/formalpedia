-- Prove2me | Theorems.Thm_pac_imp_vcdim_finite
-- name    : pac_imp_vcdim_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:30.929138+00:00
-- url     : https://prove2.me/theorems/ea41aa97-2d0d-4077-af5f-4a7967845f7d
-- title:
--   pac imp vcdim finite: pac imp vcdim finite
-- statement:
--   Direction →: PAC learnability implies finite VCDim.
--
--       PROOF ROUTE (via double-sample infrastructure in Generalization.lean):
--       Step 1: Contrapositive — assume VCDim = ∞
--       Step 2: For m = mf(ε,δ), extract S with |S| = 2m shattered by C
--         (uses WithTop.eq_top_iff_forall_ge, same as vcdim_univ_infinite)
--       Step 3: Construct D = uniform on S (Finset.uniformMeasure?)
--         KU₁₉: Mathlib's uniform measure on a finite set — does
--         `MeasureTheory.Measure.count` / `Finset.card` give IsProbabilityMeasure?
--       Step 4: Double-sample trick via GhostSample + symmetrization
--       Step 5: Counting argument on restricted labelings
--
--       **HC at this joint:** Step 3 requires constructing a specific probability measure
--       from a combinatorial object (the shattered set). This is a P₁→P₂ crossing.
--       UK₉: The construction of the hard distribution is the only non-constructive
--       step. Can it be made constructive? (Related to derandomization in learning.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L105-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L105-L111

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

theorem pac_imp_vcdim_finite (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hC : PACLearnable X C) :
    VCDim X C < ⊤ := by sorry
