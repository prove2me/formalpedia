-- Prove2me | solution 1 for mme_dwz_fourth_q5_180_endpoint_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T09:51:21.218889+00:00
-- url     : https://prove2.me/submissions/fd97825a-5629-46dd-a493-ca3b3c5f0e9a

import Definitions.Def_mme_dwz_fourth_q5_180_endpoint_bundle_data
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_solution_of_split
import Theorems.Thm_mme_dwz_fourth_elementary_MM_six_endpoints
import Theorems.Thm_mme_dwz_fourth_oneHot_actual_canonical_component_data

open MME MME.DWZFourthQ5EndpointBundle
open MME
open MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open MME.DWZFourthPublicOrdinary181
open MME.DWZFourthPrescribedZ181
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthElementaryMM
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open MME.DWZFourthPublicOrdinary181
open scoped Classical

theorem canonicalQ5_solution_120 :
    ∀ {K : Type u} [Field K] (hcentral : CentralSquarePublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))),
    PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : Real) :=
  mme_dwz_fourth_elementary_MM_six_endpoints.{u}

end MME.DWZFourthElementaryMM
namespace MME.DWZFourthPrescribedZ181.OneHotSplice
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open scoped Classical

theorem componentZProfile_eq_normalizedZProfile :
    ∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
    componentZProfile i = normalizedZProfile i :=
  mme_dwz_fourth_oneHot_40_integration_splice.{0}.1

theorem of_properSixEndpointsPointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt i.castSucc)
          ((constantComponentData tensorAt).basis i)
          ((constantComponentData tensorAt).grade i)
          (componentZProfile i) tau
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  mme_dwz_fourth_oneHot_40_integration_splice.{u}.2

end MME.DWZFourthPrescribedZ181.OneHotSplice
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
namespace MME.DWZFourthPrescribedZ181.OneHotActualCanonical
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open scoped Classical

theorem of_properSixEndpointsPointwise :
    ∀ {K : Type u} [Field K] (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (canonicalQ5Components K) i.castSucc)
          ((componentData K).basis i) ((componentData K).grade i)
          (componentZProfile i) (790643 / 1000000 : ℝ)
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  mme_dwz_fourth_oneHot_actual_canonical_component_data.{u}

end MME.DWZFourthPrescribedZ181.OneHotActualCanonical
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
namespace MME.DWZFourthPublicOrdinary181
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open scoped Classical

theorem properSixEndpointsPointwise_of_partition :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpublic : PublicComplementSixEndpoints tensorAt tau) (hpositive : PositiveFourthSixEndpoints tensorAt tau),
    ProperSixEndpointsPointwise tensorAt tau :=
  mme_dwz_fourth_public_ordinary_181_reduction.{u}.1

theorem canonicalQ5_solution :
    ∀ {K : Type u} [Field K] (hpublic : PublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hpositive : PositiveFourthSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hfinal : FinalSixExtraction (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) :=
  mme_dwz_fourth_public_ordinary_181_reduction.{u}.2

end MME.DWZFourthPublicOrdinary181

section B180Bridge
open MME MME.DWZRestrictedValue MME.DWZFourthTensorLedger MME.DWZFourthPrescribedZ181 Module

namespace B180

theorem mpr_heq {α β : Sort _} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h; rfl

theorem mp_heq' {α β : Sort _} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  subst h; rfl

theorem ledgerFin_val (i : Fin 180) : ledgerFin i.val = i.castSucc := by
  apply Fin.ext
  change i.val % 181 = i.val
  exact Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))

theorem index_eq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    extendedLedgerIndex data j.castSucc = data.ι j := by
  simp only [extendedLedgerIndex, Fin.lastCases_castSucc]

theorem width_eq (j : Fin 180) :
    ledgerZWidth j.castSucc = (componentSpecAt j).address.zWidth := by
  simp only [ledgerZWidth, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta]

theorem basis_heq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    HEq ((extendLedgerBasisGradeData data).basis j.castSucc) (data.basis j) := by
  simp only [extendLedgerBasisGradeData, Fin.lastCases_castSucc]
  exact mpr_heq _ _

theorem grade_heq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    HEq ((extendLedgerBasisGradeData data).grade j.castSucc) (data.grade j) := by
  simp only [extendLedgerBasisGradeData, Fin.lastCases_castSucc]
  apply Function.hfunext (index_eq data j)
  intro a a' haa'
  refine (mpr_heq _ _).trans ?_
  rw [eq_of_heq ((mp_heq' _ a).trans haa')]

theorem profile_heq (j : Fin 180) :
    HEq (ledgerZProfile j.castSucc) (componentZProfile j) := by
  unfold ledgerZProfile
  rw [dif_pos (show (j.castSucc : ℕ) < 180 from j.isLt)]
  refine (mpr_heq _ _).trans ?_
  rfl

/-- The prescribed-Z value only depends on basis, grade and profile up to `HEq`. -/
theorem pz_transport {K : Type u} [Field K] (T : TensorObj K 3) {ι ι' : Type u} {t t' : ℕ}
    (b : Basis ι K (T.V 2)) (b' : Basis ι' K (T.V 2)) (g : ι → Fin t) (g' : ι' → Fin t')
    (p : IntegerZSplitProfile t) (p' : IntegerZSplitProfile t')
    (hι : ι = ι') (ht : t = t') (hb : HEq b b') (hg : HEq g g') (hp : HEq p p') (τ V : ℝ) :
    HasPrescribedZSixRestrictionValueAtLeast T b g p τ V ↔
      HasPrescribedZSixRestrictionValueAtLeast T b' g' p' τ V := by
  subst hι; subst ht
  cases eq_of_heq hb; cases eq_of_heq hg; cases eq_of_heq hp
  rfl

/-- `componentValue_iff` for arbitrary component data. -/
theorem value_iff_generic {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (i : Fin 180) (τ V : ℝ) :
    LedgerPrescribedZValue (exactLedgerPrescribedZData (extendLedgerBasisGradeData data))
        i.val τ V ↔
      HasPrescribedZSixRestrictionValueAtLeast (tensorAt i.castSucc) (data.basis i)
        (data.grade i) (componentZProfile i) τ V := by
  unfold LedgerPrescribedZValue
  rw [ledgerFin_val]
  exact pz_transport (tensorAt i.castSucc) _ _ _ _ _ _ (index_eq data i) (width_eq i)
    (basis_heq data i) (grade_heq data i) (profile_heq i) τ V

end B180

end B180Bridge

namespace MME.DWZFourthQ5EndpointBundle

private theorem ledgerFin_val (i : Fin 180) :
    ledgerFin i.val = i.castSucc := by
  apply Fin.ext
  change i.val % 181 = i.val
  exact Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))

/-- On a proper row the extended 181-entry package reduces to the component
basis, grade, and generated profile literally used by the row theorems. -/
private theorem componentValue_iff
    {K : Type u} [Field K] (i : Fin 180) (V : ℝ) :
    LedgerPrescribedZValue (ledgerData K) i.val tau V ↔
      HasPrescribedZSixRestrictionValueAtLeast
        (tensorFamily K i.castSucc)
        ((componentData K).basis i) ((componentData K).grade i)
        (componentZProfile i) tau V := by
  exact B180.value_iff_generic (componentData K) i tau V

/-- All 180 ordinary component endpoints.  Exactly the central/coupled square
bundle (120 rows) and the positive fourth bundle (21 rows) remain premises;
the other 39 rows are supplied by public exact-MM theorems. -/
private theorem ordinary180
    {K : Type u} [Field K]
    (hcentral : CentralOrdinaryEndpoints K)
    (hpositive : PositiveFourthOrdinaryEndpoints K) :
    ProperSixEndpointsPointwise (tensorFamily K) tau := by
  apply properSixEndpointsPointwise_of_partition (tensorFamily K) tau
  · exact MME.DWZFourthElementaryMM.canonicalQ5_solution_120 hcentral
  · exact hpositive

/-- The forty one-hot rows, with their actual canonical component bases and
grades, are prescribed-Z endpoints at the exact stored ledger rates. -/
private theorem oneHot40
    {K : Type u} [Field K]
    (hcentral : CentralOrdinaryEndpoints K)
    (hpositive : PositiveFourthOrdinaryEndpoints K) :
    ∀ i : Fin 180,
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        LedgerPrescribedZValue (ledgerData K) i.val tau
          (Real.exp (DWZFourthPrescribedZ181.properLedgerRate i : ℝ)) := by
  intro i hi
  apply (componentValue_iff i _).2
  exact
    MME.DWZFourthPrescribedZ181.OneHotActualCanonical.of_properSixEndpointsPointwise (ordinary180 hcentral hpositive) i hi

/-- Strongest current 180-row splice.  Public exact-MM theorems and the
canonical one-hot conversion are internal; the literal/coupled endpoint
adapters plus the exact 58-row residual complete the prescribed-Z bundle. -/
private theorem prescribedZ180
    {K : Type u} [Field K]
    (hcentral : CentralOrdinaryEndpoints K)
    (hpositive : PositiveFourthOrdinaryEndpoints K)
    (hliteral : Literal022PrescribedZEndpoints K)
    (hcoupled : CoupledCyclicPrescribedZEndpoints K)
    (hresidual : ResidualPrescribedZEndpoints K) :
    ProperLedgerPrescribedZEndpoints (ledgerData K) tau := by
  apply properLedgerPrescribedZEndpoints_of_pointwise
  intro i
  by_cases hhot : hasOneHotLedgerZProfile (componentSpecAt i) = true
  · exact oneHot40 hcentral hpositive i hhot
  · by_cases hlit : publicCoverageTier (componentSpecAt i) =
        PublicCoverageTier.square022PrescribedZ
    · exact hliteral i hlit
    · by_cases hcoup : publicCoverageTier (componentSpecAt i) =
          PublicCoverageTier.square112ProfileTransport
      · exact hcoupled i hcoup
      · exact hresidual i hhot hlit hcoup

/-- The 181st/global node is now the sole structural assembly premise beyond
the row-indexed endpoint adapters above. -/
private theorem fourthValue
    {K : Type u} [Field K]
    (hcentral : CentralOrdinaryEndpoints K)
    (hpositive : PositiveFourthOrdinaryEndpoints K)
    (hliteral : Literal022PrescribedZEndpoints K)
    (hcoupled : CoupledCyclicPrescribedZEndpoints K)
    (hresidual : ResidualPrescribedZEndpoints K)
    (hfinal : FinalNodePrescribedZAssembly (ledgerData K) tau) :
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5) tau (240101 / 100 : ℝ) := by
  apply mme_dwz_fourth_prescribedZ_181_solution_of_split
  refine ⟨componentData K, ?_, ?_⟩
  · simpa [ledgerData] using
      prescribedZ180 hcentral hpositive hliteral hcoupled hresidual
  · simpa [ledgerData] using hfinal

end MME.DWZFourthQ5EndpointBundle

theorem solution :
    ∀ {K : Type u} [Field K] (hcentral : CentralOrdinaryEndpoints K) (hpositive : PositiveFourthOrdinaryEndpoints K) (hliteral : Literal022PrescribedZEndpoints K) (hcoupled : CoupledCyclicPrescribedZEndpoints K) (hresidual : ResidualPrescribedZEndpoints K) (hfinal : FinalNodePrescribedZAssembly (ledgerData K) tau),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5) tau (240101 / 100 : ℝ) :=
  fourthValue
