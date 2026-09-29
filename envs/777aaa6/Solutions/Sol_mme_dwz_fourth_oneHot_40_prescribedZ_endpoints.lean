-- Prove2me | solution 1 for mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:36:00.25922+00:00
-- url     : https://prove2.me/submissions/6b23404b-ebd9-4612-a86c-877dfc7fe4da

import Definitions.Def_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_HasPrescribedZSix_of_constant_grade_oneHot
import Theorems.Thm_mme_dwz_fourth_six_value_final_node_split

open MME MME.DWZFourthTensorLedger MME.DWZFourthTensorLedger.OneHotEndpoints
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

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

namespace MME.DWZFourthTensorLedger.OneHotEndpoints

/-- Computational content of the 40-row census: the selected grade contains
the entire denominator and every other grade has count zero. -/
private theorem normalizedZProfile_oneHot
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    ∀ a, (normalizedZProfile i).count a =
      if a = activeGrade i then
        (normalizedZProfile i).denominator else 0 := by
  decide +kernel +revert

/-- No one-hot row is one of the 63 coupled rows whose denominator/profile is
retuned by the 181-node integration.  Therefore `normalizedZProfile` agrees
definitionally with that integration's fixed `componentZProfile` on all forty
selected rows (after unfolding the latter). -/
private theorem oneHot_not_coupled
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    publicCoverageTier (componentSpecAt i) ≠
      PublicCoverageTier.square112ProfileTransport := by
  decide +kernel +revert

/-- All forty rows lift simultaneously.  The input is only the corresponding
ordinary six-value endpoints plus the genuinely tensor-specific fact that
the chosen Z-basis has the row's unique active grade. -/
private theorem headline
    {K : Type u} [Field K]
    (T : Fin 180 → TensorObj K 3)
    (ι : Fin 180 → Type u)
    (basis : (i : Fin 180) → Basis (ι i) K ((T i).V 2))
    (grade : (i : Fin 180) →
      ι i → Fin (componentSpecAt i).address.zWidth)
    (tau : ℝ) (rate : Fin 180 → ℝ)
    (hgrade : ConstantOnOneHotRows (K := K) ι grade)
    (hordinary : ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasSixSymmetricTauValueAtLeast (T i) tau
          (Real.exp (rate i))) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (T i) (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp (rate i)) := by
  intro i hi
  exact mme_HasPrescribedZSix_of_constant_grade_oneHot
    (T i) (basis i) (grade i) (normalizedZProfile i) (activeGrade i)
    (hgrade i hi) (normalizedZProfile_oneHot i hi) tau
    (Real.exp (rate i)) (Real.exp_nonneg _) (hordinary i hi)

/-- The conclusion of `headline` is attached to exactly forty distinct
entries of the fixed 180-row table. -/
private theorem attachedLedgerRowCount :
    (componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 :=
  oneHotLedgerZProfileCounts.1

/-- Direct exact-rate lift for precisely the forty-row subfamily. -/
private theorem of_oneHotProperSixEndpointsPointwise
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3)
    (ι : Fin 180 → Type u)
    (basis : (i : Fin 180) → Basis (ι i) K
      ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2))
    (grade : (i : Fin 180) →
      ι i → Fin (componentSpecAt i).address.zWidth)
    (tau : ℝ)
    (hgrade : ConstantOnOneHotRows (K := K) ι grade)
    (hordinary : OneHotProperSixEndpointsPointwise tensorAt tau) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  apply headline
    (fun i ↦ tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
    ι basis grade tau
    (fun i ↦ (DWZFourthSixFinalSplit.properLedgerRate i : ℝ))
    hgrade hordinary

/-- Exact-rate specialization for the existing 181-node ordinary endpoint
bundle.  This is the direct splice into the fourth-ledger proof: no endpoint
value or profile assumption remains on any of the forty selected rows. -/
private theorem of_properSixEndpointsPointwise
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3)
    (ι : Fin 180 → Type u)
    (basis : (i : Fin 180) → Basis (ι i) K
      ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2))
    (grade : (i : Fin 180) →
      ι i → Fin (componentSpecAt i).address.zWidth)
    (tau : ℝ)
    (hgrade : ConstantOnOneHotRows (K := K) ι grade)
    (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      tensorAt tau) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  apply of_oneHotProperSixEndpointsPointwise tensorAt ι basis grade tau
    hgrade
  intro i _
  exact hordinary i

private theorem componentConstantGrade_isConstant
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) :
    ConstantOnOneHotRows (K := K)
      (componentBasisIndex tensorAt) (componentConstantGrade tensorAt) := by
  intro i _ x
  rfl

/-- Fully instantiated forty-row result on the actual component spaces.  Once
the ordinary endpoints are supplied, neither bases, gradings nor profiles
remain as hypotheses. -/
private theorem of_oneHotProperSixEndpointsPointwise_constantData
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hordinary : OneHotProperSixEndpointsPointwise tensorAt tau) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (componentBasis tensorAt i)
          (componentConstantGrade tensorAt i)
          (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  exact of_oneHotProperSixEndpointsPointwise tensorAt
    (componentBasisIndex tensorAt) (componentBasis tensorAt)
    (componentConstantGrade tensorAt) tau
    (componentConstantGrade_isConstant tensorAt) hordinary

/-- Direct consumer for the pre-existing all-180 ordinary endpoint bundle. -/
private theorem of_properSixEndpointsPointwise_constantData
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      tensorAt tau) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (componentBasis tensorAt i)
          (componentConstantGrade tensorAt i)
          (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  apply of_oneHotProperSixEndpointsPointwise_constantData tensorAt tau
  intro i _
  exact hordinary i

end MME.DWZFourthTensorLedger.OneHotEndpoints

theorem solution :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (ι : Fin 180 → Type u) (basis : (i : Fin 180) → Basis (ι i) K ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)) (grade : (i : Fin 180) → ι i → Fin (componentSpecAt i).address.zWidth) (tau : ℝ) (hgrade : ConstantOnOneHotRows (K := K) ι grade) (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  of_properSixEndpointsPointwise
