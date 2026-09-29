-- Prove2me | solution 1 for mme_dwz_fourth_oneHot_40_integration_splice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:44:42.879984+00:00
-- url     : https://prove2.me/submissions/37a86ae6-db59-4cee-8e3f-46479f038db0

import Definitions.Def_mme_dwz_fourth_oneHot_40_integration_splice_data
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_integration
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
import Theorems.Thm_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy

open MME MME.DWZFourthPrescribedZ181 MME.DWZFourthPrescribedZ181.OneHotSplice
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger.OneHotEndpoints
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped Classical

theorem of_properSixEndpointsPointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (ι : Fin 180 → Type u) (basis : (i : Fin 180) → Basis (ι i) K ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)) (grade : (i : Fin 180) → ι i → Fin (componentSpecAt i).address.zWidth) (tau : ℝ) (hgrade : ConstantOnOneHotRows (K := K) ι grade) (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  mme_dwz_fourth_oneHot_40_prescribedZ_endpoints.{u}

end MME.DWZFourthTensorLedger.OneHotEndpoints

namespace MME.DWZFourthPrescribedZ181.OneHotSplice

/-- On a one-hot row the integration does not select its coupled-profile
branch.  Its remaining atomic normalization and raw non-atomic profile are
exactly `normalizedZProfile`. -/
private theorem componentZProfile_eq_normalizedZProfile
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    componentZProfile i = normalizedZProfile i := by
  rw [IntegerZSplitProfile.mk.injEq]
  constructor
  · decide +kernel +revert
  · funext a
    revert i a
    decide +kernel

private theorem constantComponentData_isConstant
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) :
    ConstantOnOneHotRows (K := K)
      (constantComponentData tensorAt).ι
      (constantComponentData tensorAt).grade := by
  intro i _ x
  rfl

/-- Direct exact-rate consumer of the existing ordinary endpoint bundle.
The conclusion already uses `ComponentBasisGradeData` and
`componentZProfile`, i.e. precisely the component-level data expected by the
181-node prescribed-Z integration. -/
private theorem of_properSixEndpointsPointwise
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (tau : ℝ)
    (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      tensorAt tau) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt i.castSucc)
          ((constantComponentData tensorAt).basis i)
          ((constantComponentData tensorAt).grade i)
          (componentZProfile i) tau
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  intro i hi
  have h :=
    MME.DWZFourthTensorLedger.OneHotEndpoints.of_properSixEndpointsPointwise
      tensorAt (constantComponentData tensorAt).ι
      (constantComponentData tensorAt).basis
      (constantComponentData tensorAt).grade tau
      (constantComponentData_isConstant tensorAt) hordinary i hi
  rw [← componentZProfile_eq_normalizedZProfile i hi] at h
  exact h

/-- Existential packaging in the shape needed when assembling the one-hot
rows together with the remaining 140 component families. -/
private theorem exists_componentData_of_properSixEndpointsPointwise
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (tau : ℝ)
    (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      tensorAt tau) :
    ∃ componentData : ComponentBasisGradeData tensorAt,
      ∀ (i : Fin 180),
        hasOneHotLedgerZProfile (componentSpecAt i) = true →
          HasPrescribedZSixRestrictionValueAtLeast
            (tensorAt i.castSucc)
            (componentData.basis i) (componentData.grade i)
            (componentZProfile i) tau
            (Real.exp
              (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  exact ⟨constantComponentData tensorAt,
    of_properSixEndpointsPointwise tensorAt tau hordinary⟩

/-- Literal specialization to the q=5 canonical component family. -/
private theorem canonicalQ5_of_properSixEndpointsPointwise
    {K : Type u} [Field K]
    (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (canonicalQ5Components K) i.castSucc)
          ((constantComponentData
            (tensorAt (canonicalQ5Components K))).basis i)
          ((constantComponentData
            (tensorAt (canonicalQ5Components K))).grade i)
          (componentZProfile i) (790643 / 1000000 : ℝ)
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  exact of_properSixEndpointsPointwise
    (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)
    hordinary

end MME.DWZFourthPrescribedZ181.OneHotSplice

theorem solution :
    (∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
      componentZProfile i = normalizedZProfile i) ∧
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
      ∀ (i : Fin 180),
        hasOneHotLedgerZProfile (componentSpecAt i) = true →
          HasPrescribedZSixRestrictionValueAtLeast
            (tensorAt i.castSucc)
            ((constantComponentData tensorAt).basis i)
            ((constantComponentData tensorAt).grade i)
            (componentZProfile i) tau
            (Real.exp
              (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ))) :=
  ⟨componentZProfile_eq_normalizedZProfile, of_properSixEndpointsPointwise⟩
