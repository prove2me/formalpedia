-- Prove2me | Definitions.Def_mme_dwz_fourth_prescribedZ_181_integration_data
-- name    : mme_dwz_fourth_prescribedZ_181_integration_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:07:26.3741+00:00
-- url     : https://prove2.me/theorems/0cb47dbc-1846-4cb0-b48f-53a39d8d0e64
-- title:
--   Prescribed-Z realization of the 181-node fourth-power ledger
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_prescribedZ_181_integration, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_prescribed_z_restriction_value_forget_profile_below
import Definitions.Def_mme_dwz_fourth_public_component_coverage_data
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_dwz_prescribed_z_recursive_node_finite_closure

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

namespace MME.DWZFourthPrescribedZ181

/-- Total ledger index, shared by tensor objects and their prescribed-Z data. -/
def ledgerFin (index : ℕ) : Fin 181 :=
  ⟨index % 181, Nat.mod_lt _ (by norm_num)⟩

/-- The literal q=5 base, square and fourth-power blocks used by every
generated metadata address. -/
noncomputable def canonicalQ5Components (K : Type u) [Field K] :
    Q5CanonicalComponents K where
  cwObj5 := CWObj K 5
  kron := TensorObj.kron
  cwBlock5 := fun i j k ↦
    (cwCanonicalGrading 5 (K := K)).blockSubtensor (![i, j, k])
  cwSquareBlock5 := fun i j k ↦
    (cwSquareCanonicalGrading K 5).blockSubtensor
      (cwSquareBlockType i j k)
  cwFourthBlock5 := fun i j k ↦
    StothersFourth.cwFourthConstituent K 5 i j k

/-- The exact denominator used by the structural prescribed-Z ledger.  The 63
coupled square rows use the canonical cyclic profiles certified by the public
q=5 source theorem; all other rows retain their generated denominator. -/
def componentZDenominator (i : Fin 180) : ℕ :=
  if publicCoverageTier (componentSpecAt i) =
      PublicCoverageTier.square112ProfileTransport then
    canonicalCyclicZDenominator (componentSpecAt i)
  else
    (componentSpecAt i).zDenominator

/-- The six atomic rows use `[0,0]` as a no-recursion sentinel, represented
here by the valid split `[1,0]`.  The 63 coupled rows are snapped to the exact
public cyclic shapes `[l,2g,l]` and `[l+g,l+g,0]`, including the localized
`p=1/10` retuning of objects 76/77/78.  Every other row remains verbatim. -/
def componentZCount (i : Fin 180)
    (a : Fin (componentSpecAt i).address.zWidth) : ℕ :=
  if publicCoverageTier (componentSpecAt i) =
      PublicCoverageTier.square112ProfileTransport then
    (canonicalCyclicZCounts (componentSpecAt i))[a.val]?.getD 0
  else if (componentSpecAt i).method = .atomic then
    if a.val = 0 then 1 else 0
  else
    (componentSpecAt i).zCount a

theorem componentZDenominator_pos (i : Fin 180) :
    0 < componentZDenominator i := by
  decide +kernel +revert

theorem componentZCount_sum (i : Fin 180) :
    ∑ a, componentZCount i a = componentZDenominator i := by
  decide +kernel +revert

/-- The normalized profile attached to one generated component row. -/
def componentZProfile (i : Fin 180) :
    IntegerZSplitProfile (componentSpecAt i).address.zWidth where
  denominator := componentZDenominator i
  denominator_pos := componentZDenominator_pos i
  count := componentZCount i
  count_sum := componentZCount_sum i

/-- Component widths are `2`, `3`, and `5`; the final whole tensor uses the
source-faithful one-cell profile. -/
def ledgerZWidth (i : Fin 181) : ℕ :=
  if h : i.val < 180 then
    (componentSpecAt ⟨i.val, h⟩).address.zWidth
  else 1

/-- All 180 generated integer profiles plus the trivial global profile
`denominator = 1`, `count = ![1]`. -/
def ledgerZProfile (i : Fin 181) : IntegerZSplitProfile (ledgerZWidth i) := by
  classical
  if h : i.val < 180 then
    let j : Fin 180 := ⟨i.val, h⟩
    have hw : ledgerZWidth i = (componentSpecAt j).address.zWidth := by
      simp [ledgerZWidth, h, j]
    rw [hw]
    exact componentZProfile j
  else
    have hw : ledgerZWidth i = 1 := by simp [ledgerZWidth, h]
    rw [hw]
    exact {
      denominator := 1
      denominator_pos := by norm_num
      count := fun _ ↦ 1
      count_sum := by simp }

/-- A prescribed-Z basis, grading and integral split profile for every tensor
in the 181-entry scalar traversal. -/
structure LedgerPrescribedZData {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) where
  ι : Fin 181 → Type u
  t : Fin 181 → ℕ
  basis : (i : Fin 181) → Basis (ι i) K ((tensorAt i).V 2)
  grade : (i : Fin 181) → ι i → Fin (t i)
  profile : (i : Fin 181) → IntegerZSplitProfile (t i)

/-- Only bases and compatible Z-gradings remain unspecified: every integral
profile is fixed by the generated ledger certificate. -/
structure LedgerBasisGradeData {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) where
  ι : Fin 181 → Type u
  basis : (i : Fin 181) → Basis (ι i) K ((tensorAt i).V 2)
  grade : (i : Fin 181) → ι i → Fin (ledgerZWidth i)

/-- Canonical basis/grade input is needed only for the 180 proper component
rows.  The final whole tensor receives an arbitrary basis and constant
one-cell grade below. -/
structure ComponentBasisGradeData {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) where
  ι : Fin 180 → Type u
  basis : (i : Fin 180) → Basis (ι i) K ((tensorAt i.castSucc).V 2)
  grade : (i : Fin 180) →
    ι i → Fin (componentSpecAt i).address.zWidth

/-- A fixed, noncanonical basis index for the Z-space of each proper ledger
component.  Existence is automatic over a field; choosing it here removes
basis existence from the structural hypothesis. -/
noncomputable def componentBasisIndex
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (i : Fin 180) : Type u :=
  Module.Free.ChooseBasisIndex K ((tensorAt i.castSucc).V 2)

/-- The corresponding chosen basis. -/
noncomputable def componentBasis
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (i : Fin 180) :
    Basis (componentBasisIndex tensorAt i) K ((tensorAt i.castSucc).V 2) :=
  Module.Free.chooseBasis K ((tensorAt i.castSucc).V 2)

/-- The only unresolved component-level datum is now the grading of a fixed
chosen basis.  Its compatibility with the generated profiles is tested by
the finite node-assembly premise below. -/
structure ComponentGradeData {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) where
  grade : (i : Fin 180) → componentBasisIndex tensorAt i →
    Fin (componentSpecAt i).address.zWidth

/-- Package the fixed chosen bases with component gradings. -/
noncomputable def chosenComponentBasisGradeData
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentGradeData tensorAt) :
    ComponentBasisGradeData tensorAt where
  ι := componentBasisIndex tensorAt
  basis := componentBasis tensorAt
  grade := data.grade

noncomputable def extendedLedgerIndex
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (i : Fin 181) : Type u :=
  Fin.lastCases
    (Module.Free.ChooseBasisIndex K ((tensorAt (Fin.last 180)).V 2))
    data.ι i

/-- Extend component bases/grades over the terminal tensor.  The terminal
basis is chosen noncomputably and its grade is constantly zero. -/
noncomputable def extendLedgerBasisGradeData
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) :
    LedgerBasisGradeData tensorAt where
  ι := extendedLedgerIndex data
  basis i := by
    refine Fin.lastCases
      (motive := fun i => Basis (extendedLedgerIndex data i) K
        ((tensorAt i).V 2)) ?_ ?_ i
    · simpa [extendedLedgerIndex] using
        (Module.Free.chooseBasis K ((tensorAt (Fin.last 180)).V 2))
    · intro j
      simpa [extendedLedgerIndex] using data.basis j
  grade i := by
    refine Fin.lastCases
      (motive := fun i => extendedLedgerIndex data i → Fin (ledgerZWidth i))
      ?_ ?_ i
    · intro _
      simpa [ledgerZWidth] using (0 : Fin 1)
    · intro j x
      have x' : data.ι j := by
        simpa [extendedLedgerIndex] using x
      simpa [ledgerZWidth, j.isLt] using data.grade j x'

/-- Canonical completion of basis/grading data by the exact generated split
profiles. -/
noncomputable def exactLedgerPrescribedZData
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerBasisGradeData tensorAt) : LedgerPrescribedZData tensorAt where
  ι := data.ι
  t := ledgerZWidth
  basis := data.basis
  grade := data.grade
  profile := ledgerZProfile

/-- The index-sensitive prescribed-Z value predicate replayed by the scalar
ledger. -/
def LedgerPrescribedZValue
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt)
    (index : ℕ) (tau V : ℝ) : Prop :=
  HasPrescribedZSixRestrictionValueAtLeast
    (tensorAt (ledgerFin index))
    (data.basis (ledgerFin index))
    (data.grade (ledgerFin index))
    (data.profile (ledgerFin index)) tau V

/-- The tensor-specific data for every node, after the scalar ledger has
identified the weighted child product.  Repeated child occurrences and
rational powers are represented by the finite router `childIndex`; its strict
bases multiply to the scalar product exactly. -/
def AllNodePrescribedZAssembly
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ) : Prop :=
  ∀ (prior : Array Rat) (node : Node) (weighted : Rat) (product : ℝ),
    (∀ term ∈ node.children, 0 ≤ term.2) →
    weightedPrior prior node.children = some weighted →
    weightedValueProduct prior node.children = some product →
    ChildrenRealize
      (fun index value ↦ LedgerPrescribedZValue data index tau value)
      prior node →
    ∃ (n : ℕ) (childIndex : Fin n → ℕ) (V v : Fin n → ℝ),
      product = ∏ j, v j ∧
      (∀ j, 0 < v j) ∧
      (∀ j, v j < V j) ∧
      (∀ j, LedgerPrescribedZValue data (childIndex j) tau (V j)) ∧
      PrescribedZFiniteNodeAssembly
        (tensorAt (ledgerFin prior.size))
        (fun j ↦ tensorAt (ledgerFin (childIndex j)))
        (data.basis (ledgerFin prior.size))
        (data.grade (ledgerFin prior.size))
        (data.profile (ledgerFin prior.size))
        (fun j ↦ data.basis (ledgerFin (childIndex j)))
        (fun j ↦ data.grade (ledgerFin (childIndex j)))
        (fun j ↦ data.profile (ledgerFin (childIndex j)))
        tau (Real.exp (node.retainedFloor : ℝ)) v

/-- The one bundled structural premise for the complete fourth-power proof.
The canonical API fixes all 180 component addresses through
`DWZFourthTensorLedger.tensorAt`; only bases/gradings and the per-node finite
assemblies remain tensor-specific. -/
def Fourth181StructuralPremise (K : Type u) [Field K] : Prop :=
  ∃ componentGrade : ComponentGradeData
      (tensorAt (canonicalQ5Components K)),
    AllNodePrescribedZAssembly
      (exactLedgerPrescribedZData
        (extendLedgerBasisGradeData
          (chosenComponentBasisGradeData componentGrade)))
      (790643 / 1000000 : ℝ)

/-! ## Split interface: 180 component endpoints plus one global node -/
/-- Exact rate array before the final, global ledger node. -/
def properLedgerRates : Array Rat :=
  runRates (ledger.take 180) #[]

/-- The final global node in the generated 181-node scalar ledger. -/
def globalLedgerNode : Node :=
  ledger[180]'(by decide +kernel)

theorem properLedgerRates_size : properLedgerRates.size = 180 := by
  decide +kernel

def properLedgerRate (i : Fin 180) : Rat :=
  properLedgerRates[i.val]'(by rw [properLedgerRates_size]; exact i.isLt)

/-- The first 180 prescribed-Z endpoints, with the exact rates already fixed
by the checked scalar ledger.  Component theorems can discharge these facts
independently of the global tensor extraction. -/
def ProperLedgerPrescribedZEndpoints
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ) : Prop :=
  RateRealizes
    (fun index value ↦ LedgerPrescribedZValue data index tau value)
    properLedgerRates

/-- Pointwise form of the first-180 endpoint bundle, indexed directly by the
generated component table. -/
def ProperLedgerPrescribedZEndpointsPointwise
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ) : Prop :=
  ∀ i : Fin 180,
    LedgerPrescribedZValue data i.val tau
      (Real.exp (properLedgerRate i : ℝ))

/-- The sole finite tensor assembly left at the global fourth-power node once
the 180 component endpoints are available. -/
def FinalNodePrescribedZAssembly
    {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : LedgerPrescribedZData tensorAt) (tau : ℝ) : Prop :=
  ∀ (weighted : Rat) (product : ℝ),
    (∀ term ∈ globalLedgerNode.children, 0 ≤ term.2) →
    weightedPrior properLedgerRates globalLedgerNode.children = some weighted →
    weightedValueProduct properLedgerRates globalLedgerNode.children =
      some product →
    ChildrenRealize
      (fun index value ↦ LedgerPrescribedZValue data index tau value)
      properLedgerRates globalLedgerNode →
    ∃ (n : ℕ) (childIndex : Fin n → ℕ) (V v : Fin n → ℝ),
      product = ∏ j, v j ∧
      (∀ j, 0 < v j) ∧
      (∀ j, v j < V j) ∧
      (∀ j, LedgerPrescribedZValue data (childIndex j) tau (V j)) ∧
      PrescribedZFiniteNodeAssembly
        (tensorAt (ledgerFin properLedgerRates.size))
        (fun j ↦ tensorAt (ledgerFin (childIndex j)))
        (data.basis (ledgerFin properLedgerRates.size))
        (data.grade (ledgerFin properLedgerRates.size))
        (data.profile (ledgerFin properLedgerRates.size))
        (fun j ↦ data.basis (ledgerFin (childIndex j)))
        (fun j ↦ data.grade (ledgerFin (childIndex j)))
        (fun j ↦ data.profile (ledgerFin (childIndex j)))
        tau (Real.exp (globalLedgerNode.retainedFloor : ℝ)) v

/-- Refined structural premise: component endpoints and the one global finite
assembly are separated, so public component endpoints never have to be routed
through a generic per-node assembly hypothesis. -/
def Fourth181SplitStructuralPremise (K : Type u) [Field K] : Prop :=
  ∃ componentData : ComponentBasisGradeData
      (tensorAt (canonicalQ5Components K)),
    let data := exactLedgerPrescribedZData
      (extendLedgerBasisGradeData componentData)
    ProperLedgerPrescribedZEndpoints data (790643 / 1000000 : ℝ) ∧
      FinalNodePrescribedZAssembly data (790643 / 1000000 : ℝ)

end MME.DWZFourthPrescribedZ181


