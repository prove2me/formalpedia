-- Prove2me | solution 1 for mme_dwz_fourth_prescribedZ_181_solution_of_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T06:31:07.783743+00:00
-- url     : https://prove2.me/submissions/5d12720a-6796-4f7e-84b0-6f55323864be

import Definitions.Def_mme_dwz_fourth_prescribedZ_181_integration_data
import Theorems.Thm_mme_dwz_prescribed_z_restriction_value_forget_profile_below
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_dwz_prescribed_z_recursive_node_finite_closure

open MME MME.DWZFourthPrescribedZ181
open BigOperators Module
open MME
open DWZComponentRestriction DWZRestrictedValue
open DWZFourthScalarLedger
open DWZFourthScalarLedgerInduction
open DWZFourthTensorLedger
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthScalarLedger
open scoped Classical

theorem exactRationalRecurrenceCertificate :
    checkLedger = true /\ naturalRateFloor <= finalRateFloor :=
  mme_dwz_fourth_exact_scalar_recurrence_ledger_ma.1

theorem exactRationalRecurrenceCertificateReal :
    (naturalRateFloor : Real) <= (finalRateFloor : Real) :=
  mme_dwz_fourth_exact_scalar_recurrence_ledger_ma.2

end MME.DWZFourthScalarLedger
namespace MME.DWZFourthTensorLedger
open scoped Classical

theorem oneHotLedgerZProfileCounts :
    (componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .atomicExactMM).length = 6 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .squareElementaryBoundary).length = 5 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .square022CyclicTransport).length = 19 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .fourthElementaryBoundary).length = 10 :=
  mme_dwz_fourth_public_component_coverage.1

theorem componentSpecAt_mem_componentMetadata :
    ∀ (i : Fin 180),
    componentSpecAt i ∈ componentMetadata.toList :=
  mme_dwz_fourth_public_component_coverage.2.1

theorem canonicalCyclicLedgerPremisesProp :
    ∀ (metadata : ComponentMetadata) (hmem : metadata ∈ componentMetadata.toList) (htier : publicCoverageTier metadata = PublicCoverageTier.square112ProfileTransport),
    let l := canonicalCyclicL metadata
    let g := canonicalCyclicG metadata
    341 * l < 100 * g ∧
      canonicalCyclicZDenominator metadata = 2 * (l + g) ∧
      CanonicalCyclicProfileShape metadata :=
  mme_dwz_fourth_public_component_coverage.2.2

end MME.DWZFourthTensorLedger
namespace MME.DWZFourthScalarLedgerInduction
open MME.DWZFourthScalarLedger
open MME
open scoped Classical

theorem nodeAccepts_facts :
    ∀ (prior : Array Rat) (node : Node) (hnode : nodeAccepts prior node = true),
    (∀ term ∈ node.children, 0 ≤ term.2) ∧
      ∃ weighted,
        weightedPrior prior node.children = some weighted ∧
          node.rateFloor ≤ weighted + node.retainedFloor :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{0}.1

theorem exactLedgerFinalComponentValue :
    ∀ (ValueAtLeast : Nat → ℝ → Prop) (hclosure : NodeClosure ValueAtLeast),
    ValueAtLeast 180 (Real.exp (finalRateFloor : ℝ)) :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{0}.2.1

theorem weightedValueProduct_eq_exp :
    ∀ (prior : Array Rat) (terms : List (Prod Nat Rat)) (weighted : Rat) (hweighted : weightedPrior prior terms = some weighted),
    weightedValueProduct prior terms = some (Real.exp (weighted : ℝ)) :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{0}.2.2.1

theorem childrenRealize_of_weightedPrior :
    ∀ (ValueAtLeast : Nat → ℝ → Prop) (prior : Array Rat) (node : Node) (weighted : Rat) (hweighted : weightedPrior prior node.children = some weighted) (hprior : RateRealizes ValueAtLeast prior),
    ChildrenRealize ValueAtLeast prior node :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{0}.2.2.2.1

theorem exp_rateFloor_le_weighted_product :
    ∀ (node : Node) (weighted : Rat) (hbound : node.rateFloor ≤ weighted + node.retainedFloor),
    Real.exp (node.rateFloor : ℝ) ≤
      Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ) :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{0}.2.2.2.2.1

theorem exactLedgerTensorFamilyFourthValue :
    ∀ {K : Type u} [Field K] (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop) (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hmono : ∀ T A B, 0 ≤ A → A ≤ B → SixValueAtLeast T tau B → SixValueAtLeast T tau A) (hextraction : TensorRecursiveExtraction SixValueAtLeast tensorAt tau),
    SixValueAtLeast (tensorAt ⟨180, by norm_num⟩) tau
      (240101 / 100 : ℝ) :=
  mme_dwz_fourth_scalar_ledger_induction_facade.{u}.2.2.2.2.2

end MME.DWZFourthScalarLedgerInduction
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
namespace MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

theorem fourth_value_exceeds_2401_01_of_natural_rate_floor :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate :=
  mme_dwz_fourth_terminal_log_margin

end MME.DWZFourthScalar

namespace MME.DWZFourthPrescribedZ181

/-- The exact row-level interface to `f432e635` and `5fb56126`: every coupled
profile used by the 181-node ledger has a balanced public source parameter,
the required denominator, the correct literal/cyclic shape, and exactly the
count function stored in `componentZProfile`. -/
private theorem componentZProfile_coupled_public_certificate
    (i : Fin 180)
    (hi : publicCoverageTier (componentSpecAt i) =
      PublicCoverageTier.square112ProfileTransport) :
    let metadata := componentSpecAt i
    let l := canonicalCyclicL metadata
    let g := canonicalCyclicG metadata
    341 * l < 100 * g ∧
      (componentZProfile i).denominator = 2 * (l + g) ∧
      CanonicalCyclicProfileShape metadata ∧
      ∀ a, (componentZProfile i).count a =
        (canonicalCyclicZCounts metadata)[a.val]?.getD 0 := by
  dsimp only
  rcases canonicalCyclicLedgerPremisesProp (componentSpecAt i)
      (componentSpecAt_mem_componentMetadata i) hi with
    ⟨hbalance, hden, horientation⟩
  refine ⟨hbalance, ?_, horientation, ?_⟩
  · simpa [componentZProfile, componentZDenominator, hi] using hden
  · intro a
    simp [componentZProfile, componentZCount, hi]

private theorem ledgerZProfile_final_denominator :
    (ledgerZProfile (ledgerFin 180)).denominator = 1 := by
  decide +kernel

private theorem ledgerZProfile_final_count :
    (ledgerZProfile (ledgerFin 180)).count = fun _ ↦ 1 := by
  funext i
  fin_cases i
  decide +kernel

private theorem globalLedgerNode_accepts :
    nodeAccepts properLedgerRates globalLedgerNode = true := by
  decide +kernel

private theorem globalLedgerNode_rateFloor :
    globalLedgerNode.rateFloor = finalRateFloor := by
  decide +kernel

private theorem properLedgerPrescribedZEndpoints_of_pointwise
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ)
    (h : ProperLedgerPrescribedZEndpointsPointwise data tau) :
    ProperLedgerPrescribedZEndpoints data tau := by
  intro index rate hlookup
  have hindex : index < properLedgerRates.size :=
    (Array.getElem?_eq_some_iff.mp hlookup).choose
  have hindex180 : index < 180 := by
    simpa [properLedgerRates_size] using hindex
  let i : Fin 180 := ⟨index, hindex180⟩
  have hrate : properLedgerRate i = rate := by
    have := (Array.getElem?_eq_some_iff.mp hlookup).choose_spec
    simpa [properLedgerRate, i] using this
  simpa [hrate] using h i

private theorem prescribedZValue_mono_endpoint
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt)
    (index : ℕ) (tau A B : ℝ)
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : LedgerPrescribedZValue data index tau B) :
    LedgerPrescribedZValue data index tau A := by
  rcases hB with ⟨hB0, hB⟩
  refine ⟨hA, ?_⟩
  intro W hW hWA cutoff
  exact hB W hW (hWA.trans_le hAB) cutoff

private theorem nodeClosure_of_allNodeAssembly
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ)
    (hall : AllNodePrescribedZAssembly data tau) :
    NodeClosure
      (fun index value ↦ LedgerPrescribedZValue data index tau value) := by
  intro prior node weighted hnonnegative hweighted hbound hprior
  have hproduct := weightedValueProduct_eq_exp
    prior node.children weighted hweighted
  have hchildren := childrenRealize_of_weightedPrior
    (fun index value ↦ LedgerPrescribedZValue data index tau value)
    prior node weighted hweighted hprior
  obtain ⟨n, childIndex, V, v, hproductEq,
      hpos, hstrict, hvalue, hassembly⟩ :=
    hall prior node weighted (Real.exp (weighted : ℝ))
      hnonnegative hweighted hproduct hchildren
  have hlarge : LedgerPrescribedZValue data prior.size tau
      (Real.exp (node.retainedFloor : ℝ) * ∏ j, v j) := by
    exact mme_dwz_prescribed_z_recursive_node_finite_closure
      (tensorAt (ledgerFin prior.size))
      (fun j ↦ tensorAt (ledgerFin (childIndex j)))
      (data.basis (ledgerFin prior.size))
      (data.grade (ledgerFin prior.size))
      (data.profile (ledgerFin prior.size))
      (fun j ↦ data.basis (ledgerFin (childIndex j)))
      (fun j ↦ data.grade (ledgerFin (childIndex j)))
      (fun j ↦ data.profile (ledgerFin (childIndex j)))
      tau (Real.exp (node.retainedFloor : ℝ)) V v
      (Real.exp_pos _).le hpos hstrict hvalue hassembly
  rw [← hproductEq] at hlarge
  exact prescribedZValue_mono_endpoint data prior.size tau
    (Real.exp (node.rateFloor : ℝ))
    (Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ))
    (Real.exp_pos _).le
    (exp_rateFloor_le_weighted_product node weighted hbound) hlarge

/-- The fully specialized fourth-power endpoint.  All scalar recurrence,
terminal-log arithmetic, common-length synchronization, cofinality, and
finite product arithmetic are discharged. -/
private theorem headline
    {K : Type u} [Field K]
    (hstructure : Fourth181StructuralPremise K) :
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) := by
  obtain ⟨componentGrade, hall⟩ := hstructure
  let api := canonicalQ5Components K
  let data := exactLedgerPrescribedZData
    (extendLedgerBasisGradeData
      (chosenComponentBasisGradeData componentGrade))
  have hprescribed : LedgerPrescribedZValue data 180
      (790643 / 1000000 : ℝ)
      (Real.exp (finalRateFloor : ℝ)) :=
    exactLedgerFinalComponentValue
      (fun index value ↦ LedgerPrescribedZValue data index
        (790643 / 1000000 : ℝ) value)
      (nodeClosure_of_allNodeAssembly data
        (790643 / 1000000 : ℝ) hall)
  have htarget : (240101 / 100 : ℝ) <
      Real.exp (finalRateFloor : ℝ) := by
    apply MME.DWZFourthScalar.fourth_value_exceeds_2401_01_of_natural_rate_floor
    simpa [MME.DWZFourthScalar.naturalRateFloor, naturalRateFloor] using
      exactRationalRecurrenceCertificateReal
  have hsix : HasSixSymmetricTauValueAtLeast
      (tensorAt api (ledgerFin 180))
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) := by
    exact mme_dwz_prescribed_z_restriction_value_forget_profile_below
      (tensorAt api (ledgerFin 180))
      (data.basis (ledgerFin 180))
      (data.grade (ledgerFin 180))
      (data.profile (ledgerFin 180))
      (790643 / 1000000 : ℝ)
      (Real.exp (finalRateFloor : ℝ)) (240101 / 100 : ℝ)
      (by norm_num) htarget hprescribed
  have hpublic : api.cwFourthObj5 = StothersFourth.cwFourthObj K 5 := by
    simp [api, canonicalQ5Components, Q5CanonicalComponents.cwFourthObj5,
      StothersFourth.cwFourthObj]
  have hfinal : tensorAt api (ledgerFin 180) =
      StothersFourth.cwFourthObj K 5 := by
    calc
      tensorAt api (ledgerFin 180) = api.cwFourthObj5 := by
        simpa [ledgerFin] using tensorAt_final_eq_cwFourthObj5 api
      _ = StothersFourth.cwFourthObj K 5 := hpublic
  rw [hfinal] at hsix
  exact hsix

/-- The same fourth-power endpoint through the split interface.  All recursive
scalar bookkeeping is absent from the remaining global premise: it is invoked
once, at the 181st node, after the 180 exact component endpoints are loaded. -/
private theorem solution_of_split
    {K : Type u} [Field K]
    (hstructure : Fourth181SplitStructuralPremise K) :
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) := by
  obtain ⟨componentData, hproper, hglobal⟩ := hstructure
  let api := canonicalQ5Components K
  let data := exactLedgerPrescribedZData
    (extendLedgerBasisGradeData componentData)
  change ProperLedgerPrescribedZEndpoints data
    (790643 / 1000000 : ℝ) at hproper
  change FinalNodePrescribedZAssembly data
    (790643 / 1000000 : ℝ) at hglobal
  obtain ⟨hnonnegative, weighted, hweighted, hbound⟩ :=
    nodeAccepts_facts properLedgerRates globalLedgerNode
      globalLedgerNode_accepts
  have hproduct := weightedValueProduct_eq_exp
    properLedgerRates globalLedgerNode.children weighted hweighted
  have hchildren := childrenRealize_of_weightedPrior
    (fun index value ↦ LedgerPrescribedZValue data index
      (790643 / 1000000 : ℝ) value)
    properLedgerRates globalLedgerNode weighted hweighted hproper
  obtain ⟨n, childIndex, V, v, hproductEq,
      hpos, hstrict, hvalue, hassembly⟩ :=
    hglobal weighted (Real.exp (weighted : ℝ))
      hnonnegative hweighted hproduct hchildren
  have hlarge : LedgerPrescribedZValue data properLedgerRates.size
      (790643 / 1000000 : ℝ)
      (Real.exp (globalLedgerNode.retainedFloor : ℝ) * ∏ j, v j) := by
    exact mme_dwz_prescribed_z_recursive_node_finite_closure
      (tensorAt api (ledgerFin properLedgerRates.size))
      (fun j ↦ tensorAt api (ledgerFin (childIndex j)))
      (data.basis (ledgerFin properLedgerRates.size))
      (data.grade (ledgerFin properLedgerRates.size))
      (data.profile (ledgerFin properLedgerRates.size))
      (fun j ↦ data.basis (ledgerFin (childIndex j)))
      (fun j ↦ data.grade (ledgerFin (childIndex j)))
      (fun j ↦ data.profile (ledgerFin (childIndex j)))
      (790643 / 1000000 : ℝ)
      (Real.exp (globalLedgerNode.retainedFloor : ℝ)) V v
      (Real.exp_pos _).le hpos hstrict hvalue hassembly
  rw [← hproductEq] at hlarge
  have hnode : LedgerPrescribedZValue data properLedgerRates.size
      (790643 / 1000000 : ℝ)
      (Real.exp (globalLedgerNode.rateFloor : ℝ)) :=
    prescribedZValue_mono_endpoint data properLedgerRates.size
      (790643 / 1000000 : ℝ)
      (Real.exp (globalLedgerNode.rateFloor : ℝ))
      (Real.exp (globalLedgerNode.retainedFloor : ℝ) *
        Real.exp (weighted : ℝ))
      (Real.exp_pos _).le
      (exp_rateFloor_le_weighted_product globalLedgerNode weighted hbound)
      hlarge
  rw [properLedgerRates_size, globalLedgerNode_rateFloor] at hnode
  have htarget : (240101 / 100 : ℝ) <
      Real.exp (finalRateFloor : ℝ) := by
    apply MME.DWZFourthScalar.fourth_value_exceeds_2401_01_of_natural_rate_floor
    simpa [MME.DWZFourthScalar.naturalRateFloor, naturalRateFloor] using
      exactRationalRecurrenceCertificateReal
  have hsix : HasSixSymmetricTauValueAtLeast
      (tensorAt api (ledgerFin 180))
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) := by
    exact mme_dwz_prescribed_z_restriction_value_forget_profile_below
      (tensorAt api (ledgerFin 180))
      (data.basis (ledgerFin 180))
      (data.grade (ledgerFin 180))
      (data.profile (ledgerFin 180))
      (790643 / 1000000 : ℝ)
      (Real.exp (finalRateFloor : ℝ)) (240101 / 100 : ℝ)
      (by norm_num) htarget hnode
  have hpublic : api.cwFourthObj5 = StothersFourth.cwFourthObj K 5 := by
    simp [api, canonicalQ5Components, Q5CanonicalComponents.cwFourthObj5,
      StothersFourth.cwFourthObj]
  have hfinal : tensorAt api (ledgerFin 180) =
      StothersFourth.cwFourthObj K 5 := by
    calc
      tensorAt api (ledgerFin 180) = api.cwFourthObj5 := by
        simpa [ledgerFin] using tensorAt_final_eq_cwFourthObj5 api
      _ = StothersFourth.cwFourthObj K 5 := hpublic
  rw [hfinal] at hsix
  exact hsix

end MME.DWZFourthPrescribedZ181

theorem solution :
    ∀ {K : Type u} [Field K] (hstructure : Fourth181SplitStructuralPremise K),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) :=
  solution_of_split
