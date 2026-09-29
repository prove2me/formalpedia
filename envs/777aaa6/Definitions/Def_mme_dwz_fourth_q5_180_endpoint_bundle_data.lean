-- Prove2me | Definitions.Def_mme_dwz_fourth_q5_180_endpoint_bundle_data
-- name    : mme_dwz_fourth_q5_180_endpoint_bundle_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T06:06:38.088679+00:00
-- url     : https://prove2.me/theorems/1c10d7df-3140-4ddc-9914-3cee79c39baa
-- title:
--   The q=5 fourth-power value from 180 endpoints and one global node
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_q5_180_endpoint_bundle, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_elementary_MM_six_endpoints_data
import Theorems.Thm_mme_dwz_fourth_elementary_MM_six_endpoints
import Definitions.Def_mme_dwz_fourth_oneHot_actual_canonical_component_data_data
import Theorems.Thm_mme_dwz_fourth_oneHot_actual_canonical_component_data

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

namespace MME.DWZFourthQ5EndpointBundle

noncomputable abbrev tau : ℝ := 790643 / 1000000

noncomputable abbrev tensorFamily
    (K : Type u) [Field K] : Fin 181 → TensorObj K 3 :=
  tensorAt (canonicalQ5Components K)

/-- The coherent canonical component bases and first-factor fine grades used
both by the forty one-hot rows and by the recursive component interfaces. -/
noncomputable abbrev componentData
    (K : Type u) [Field K] : ComponentBasisGradeData (tensorFamily K) :=
  MME.DWZFourthPrescribedZ181.OneHotActualCanonical.componentData K

/-- The full 181-entry prescribed-Z data obtained by adding the fixed ledger
profiles and the terminal one-cell profile to `componentData`. -/
noncomputable def ledgerData
    (K : Type u) [Field K] : LedgerPrescribedZData (tensorFamily K) :=
  exactLedgerPrescribedZData
    (extendLedgerBasisGradeData (componentData K))

/-- Exact ordinary input still needed after the 39 atomic, elementary-square,
and elementary-fourth MM endpoints have been discharged.  Its cardinality is
120. -/
abbrev CentralOrdinaryEndpoints
    (K : Type u) [Field K] : Prop :=
  MME.DWZFourthElementaryMM.CentralSquarePublicComplementSixEndpoints
    (tensorFamily K)

/-- The 21 positive fourth constituents retain their ordinary endpoint
premise. -/
abbrev PositiveFourthOrdinaryEndpoints
    (K : Type u) [Field K] : Prop :=
  PositiveFourthSixEndpoints (tensorFamily K) tau

/-- Prescribed-Z adapters for the 19 literal canonical `022` rows.  The public
literal endpoint theorem supplies the mathematical endpoint; this interface
isolates only its basis/profile and ledger-rate normalization. -/
def Literal022PrescribedZEndpoints
    (K : Type u) [Field K] : Prop :=
  ∀ i : Fin 180,
    publicCoverageTier (componentSpecAt i) =
        PublicCoverageTier.square022PrescribedZ →
      LedgerPrescribedZValue (ledgerData K) i.val tau
        (Real.exp (DWZFourthPrescribedZ181.properLedgerRate i : ℝ))

/-- Prescribed-Z adapters for all 63 canonicalized cyclic `112/121/211`
rows.  Their profiles already satisfy the public source theorem's exact
integer shapes and balance inequalities. -/
def CoupledCyclicPrescribedZEndpoints
    (K : Type u) [Field K] : Prop :=
  ∀ i : Fin 180,
    publicCoverageTier (componentSpecAt i) =
        PublicCoverageTier.square112ProfileTransport →
      LedgerPrescribedZValue (ledgerData K) i.val tau
        (Real.exp (DWZFourthPrescribedZ181.properLedgerRate i : ℝ))

/-- The exact residual after combining forty one-hot rows, nineteen literal
`022` rows, and sixty-three cyclic coupled rows. -/
def ResidualPrescribedZEndpoints
    (K : Type u) [Field K] : Prop :=
  ∀ i : Fin 180,
    hasOneHotLedgerZProfile (componentSpecAt i) ≠ true →
    publicCoverageTier (componentSpecAt i) ≠
        PublicCoverageTier.square022PrescribedZ →
    publicCoverageTier (componentSpecAt i) ≠
        PublicCoverageTier.square112ProfileTransport →
      LedgerPrescribedZValue (ledgerData K) i.val tau
        (Real.exp (DWZFourthPrescribedZ181.properLedgerRate i : ℝ))

def residualIndexSet : Finset (Fin 180) :=
  Finset.univ.filter fun i ↦
    hasOneHotLedgerZProfile (componentSpecAt i) ≠ true ∧
      publicCoverageTier (componentSpecAt i) ≠
        PublicCoverageTier.square022PrescribedZ ∧
      publicCoverageTier (componentSpecAt i) ≠
        PublicCoverageTier.square112ProfileTransport

def residualObjectIds : List Nat :=
  componentMetadata.toList.filterMap fun metadata ↦
    if hasOneHotLedgerZProfile metadata ≠ true ∧
        publicCoverageTier metadata ≠
          PublicCoverageTier.square022PrescribedZ ∧
        publicCoverageTier metadata ≠
          PublicCoverageTier.square112ProfileTransport then
      some metadata.objectId
    else none

end MME.DWZFourthQ5EndpointBundle


