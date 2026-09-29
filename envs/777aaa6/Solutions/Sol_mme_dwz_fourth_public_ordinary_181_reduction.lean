-- Prove2me | solution 1 for mme_dwz_fourth_public_ordinary_181_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:27:41.313476+00:00
-- url     : https://prove2.me/submissions/2bedaf4a-bdb8-4cce-9457-50aacaec50b9

import Definitions.Def_mme_dwz_fourth_public_ordinary_181_reduction_data
import Theorems.Thm_mme_dwz_fourth_six_value_final_node_split
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_integration

open MME MME.DWZFourthPublicOrdinary181
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthPrescribedZ181
open BigOperators Module
open MME
open DWZComponentRestriction DWZRestrictedValue
open DWZFourthScalarLedger
open DWZFourthScalarLedgerInduction
open DWZFourthTensorLedger
open scoped Classical

theorem properLedgerPrescribedZEndpoints_of_pointwise :
    ∀ {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3} (data : LedgerPrescribedZData tensorAt) (tau : ℝ) (h : ProperLedgerPrescribedZEndpointsPointwise data tau),
    ProperLedgerPrescribedZEndpoints data tau :=
  mme_dwz_fourth_prescribedZ_181_integration.{u}.1

theorem headline :
    ∀ {K : Type u} [Field K] (hstructure : Fourth181StructuralPremise K),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) :=
  mme_dwz_fourth_prescribedZ_181_integration.{u}.2

end MME.DWZFourthPrescribedZ181
namespace MME.DWZFourthSixFinalSplit
open MME
open MME.DWZFourthScalarLedger
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

theorem properSixEndpoints_of_pointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpointwise : ProperSixEndpointsPointwise tensorAt tau),
    ProperSixEndpoints tensorAt tau :=
  mme_dwz_fourth_six_value_final_node_split.{u}.1

theorem headline :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hproper : ProperSixEndpoints tensorAt tau) (hglobal : FinalSixExtraction tensorAt tau),
    HasSixSymmetricTauValueAtLeast
      (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ) :=
  mme_dwz_fourth_six_value_final_node_split.{u}.2

end MME.DWZFourthSixFinalSplit
namespace MME.DWZFourthTensorLedger
open MME
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

theorem tensorAt_component :
    ∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K) (index : Fin 180),
    tensorAt api (componentLedgerIndex index) =
      api.component (componentSpecAt index).address :=
  mme_dwz_fourth_tensor_ledger_metadata.{u}.1

theorem tensorAt_final_eq_cwFourthObj5 :
    ∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K),
    tensorAt api ⟨180, by norm_num⟩ = api.cwFourthObj5 :=
  mme_dwz_fourth_tensor_ledger_metadata.{u}.2

end MME.DWZFourthTensorLedger

namespace MME.DWZFourthPublicOrdinary181

private theorem properSixEndpointsPointwise_of_partition
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hpublic : PublicComplementSixEndpoints tensorAt tau)
    (hpositive : PositiveFourthSixEndpoints tensorAt tau) :
    ProperSixEndpointsPointwise tensorAt tau := by
  intro index
  by_cases hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.fourthPositivePrescribedZOpen
  · exact hpositive index hrow
  · exact hpublic index hrow

private theorem headline
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hpublic : PublicComplementSixEndpoints tensorAt tau)
    (hpositive : PositiveFourthSixEndpoints tensorAt tau)
    (hfinal : FinalSixExtraction tensorAt tau) :
    HasSixSymmetricTauValueAtLeast
      (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ) := by
  apply mme_dwz_fourth_six_value_final_node_split.2 tensorAt tau
  · apply properSixEndpoints_of_pointwise tensorAt tau
    exact properSixEndpointsPointwise_of_partition tensorAt tau
      hpublic hpositive
  · exact hfinal

/-- Source-faithful q=5 specialization at the mission exponent.  The only
non-public row class in this interface is the explicit 21-element positive
fourth frontier; the other structural premise is the unique final node. -/
private theorem canonicalQ5_solution
    {K : Type u} [Field K]
    (hpublic : PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : ℝ))
    (hpositive : PositiveFourthSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : ℝ))
    (hfinal : FinalSixExtraction
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : ℝ)) :
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) := by
  let api := MME.DWZFourthPrescribedZ181.canonicalQ5Components K
  have hvalue := headline (tensorAt api) (790643 / 1000000 : ℝ)
    hpublic hpositive hfinal
  have hfinalTensor :
      tensorAt api ⟨180, by norm_num⟩ = StothersFourth.cwFourthObj K 5 := by
    rw [tensorAt_final_eq_cwFourthObj5]
    simp only [api, MME.DWZFourthPrescribedZ181.canonicalQ5Components,
      Q5CanonicalComponents.cwFourthObj5,
      StothersFourth.cwFourthObj]
  simpa only [hfinalTensor] using hvalue

end MME.DWZFourthPublicOrdinary181

theorem solution :
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpublic : PublicComplementSixEndpoints tensorAt tau) (hpositive : PositiveFourthSixEndpoints tensorAt tau),
      ProperSixEndpointsPointwise tensorAt tau) ∧
    (∀ {K : Type u} [Field K] (hpublic : PublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hpositive : PositiveFourthSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hfinal : FinalSixExtraction (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
      HasSixSymmetricTauValueAtLeast
        (StothersFourth.cwFourthObj K 5)
        (790643 / 1000000 : ℝ) (240101 / 100 : ℝ)) :=
  ⟨properSixEndpointsPointwise_of_partition, canonicalQ5_solution⟩
