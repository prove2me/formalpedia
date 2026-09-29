-- Prove2me | Definitions.Def_mme_dwz_fourth_oneHot_actual_canonical_component_data_data
-- name    : mme_dwz_fourth_oneHot_actual_canonical_component_data_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:45:57.848243+00:00
-- url     : https://prove2.me/theorems/f96385f3-9d2f-4d0a-923e-e24967a96467
-- title:
--   Canonical component data for the one-hot fourth-power rows
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_oneHot_actual_canonical_component_data, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_oneHot_40_integration_splice_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_integration_splice

open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open scoped Classical

universe u v

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

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

namespace MME.DWZFourthPrescribedZ181.OneHotActualCanonical

/-! ## Universe-polymorphic restricted basis -/
def GradeFiber {ι : Type v} {κ : Type*} (grade : ι → κ) (a : κ) :
    Type v :=
  {i : ι // grade i = a}

private theorem gradeFiber_span_eq
    {K V : Type u} {ι : Type v} {κ : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (grade : ι → κ) (a : κ) :
    Submodule.span K
        (Set.range (fun p : GradeFiber grade a ↦ b p.1)) =
      cwBasisGrade b grade a := by
  unfold cwBasisGrade
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- Canonical basis of one `cwBasisGrade` fiber, with independent index and
coefficient universes. -/
noncomputable def gradeFiberBasis
    {K V : Type u} {ι : Type v} {κ : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (grade : ι → κ) (a : κ) :
    Basis (GradeFiber grade a) K (cwBasisGrade b grade a) := by
  let values : GradeFiber grade a → V := fun p ↦ b p.1
  have independent : LinearIndependent K values :=
    b.linearIndependent.comp
      (fun p : GradeFiber grade a ↦ p.1) Subtype.val_injective
  let spanBasis := Basis.span independent
  let identify : Submodule.span K (Set.range values) ≃ₗ[K]
      cwBasisGrade b grade a :=
    LinearEquiv.ofEq _ _ (gradeFiber_span_eq b grade a)
  exact spanBasis.map identify

/-! ## Literal q=5 address data -/
noncomputable def canonicalAddressTensor
    (K : Type u) [Field K] : ComponentAddress → TensorObj K 3
  | .base I J L =>
      (cwCanonicalGrading 5 (K := K)).blockSubtensor (![I, J, L])
  | .square I J L =>
      (cwSquareCanonicalGrading K 5).blockSubtensor
        (cwSquareBlockType I J L)
  | .fourth I J L =>
      StothersFourth.cwFourthConstituent K 5 I J L

/-- Same-universe canonical basis index for the Z-space of an address.
Base rows are terminal atomic leaves and may use an arbitrary basis.  Square
and fourth rows use the literal public canonical grade-fiber subtypes. -/
noncomputable def CanonicalAddressZIndex
    (K : Type u) [Field K] : ComponentAddress → Type u
  | .base I J L =>
      Module.Free.ChooseBasisIndex K
        (((cwCanonicalGrading 5 (K := K)).blockSubtensor (![I, J, L])).V 2)
  | .square _ _ L =>
      ULift.{u} (GradeFiber (cwSquarePairGrade 5) L)
  | .fourth _ _ L =>
      ULift.{u} (GradeFiber (StothersFourth.cwFourthPairGrade 5) L)

/-- First-factor fine grade on the canonical square/fourth fiber; the atomic
leaf convention is the integration's normalized constant grade zero. -/
noncomputable def canonicalAddressZGrade
    (K : Type u) [Field K] (address : ComponentAddress) :
    CanonicalAddressZIndex K address → Fin address.zWidth := by
  cases address with
  | base I J L =>
      change CanonicalAddressZIndex K (.base I J L) → Fin 2
      exact fun _ ↦ 0
  | square I J L =>
      exact fun ab ↦ cwSquareCoordGrade 5 ab.down.1.1
  | fourth I J L =>
      exact fun p ↦ cwSquarePairGrade 5 p.down.1.1

/-- Basis of the actual Z-mode vector space of each literal canonical
component. -/
noncomputable def canonicalAddressZBasis
    (K : Type u) [Field K] (address : ComponentAddress) :
    Basis (CanonicalAddressZIndex K address) K
      ((canonicalAddressTensor K address).V 2) := by
  cases address with
  | base I J L =>
      exact Module.Free.chooseBasis K
        (((cwCanonicalGrading 5 (K := K)).blockSubtensor (![I, J, L])).V 2)
  | square I J L =>
      let b := gradeFiberBasis
        (cwSquareCanonicalBasis K 5 (2 : Fin 3))
        (cwSquarePairGrade 5) L
      let lifted := b.reindex (Equiv.ulift.{u}).symm
      simpa [canonicalAddressTensor, CanonicalAddressZIndex,
        TensorObj.TypeGrading.blockSubtensor,
        TensorObj.TypeGrading.classOf, cwSquareCanonicalGrading,
        cwSquareBlockType] using lifted
  | fourth I J L =>
      let b := gradeFiberBasis
        (StothersFourth.cwFourthCanonicalBasis K 5 (2 : Fin 3))
        (StothersFourth.cwFourthPairGrade 5) L
      let lifted := b.reindex (Equiv.ulift.{u}).symm
      simpa [canonicalAddressTensor, CanonicalAddressZIndex,
        StothersFourth.cwFourthConstituent,
        TensorObj.TypeGrading.blockSubtensor,
        TensorObj.TypeGrading.classOf,
        StothersFourth.cwFourthCanonicalGrading,
        StothersFourth.cwFourthBlockType] using lifted

/-- One coherent basis/grade family on the actual 180 q=5 component spaces.
It is canonical on all square/fourth rows, so the non-one-hot recursive
endpoint families can use the same data. -/
noncomputable def componentData
    (K : Type u) [Field K] :
    ComponentBasisGradeData (tensorAt (canonicalQ5Components K)) where
  ι i := CanonicalAddressZIndex K (componentSpecAt i).address
  basis i := by
    have hindex : i.castSucc = componentLedgerIndex i := by
      apply Fin.ext
      rfl
    rw [hindex, tensorAt_component]
    simpa [canonicalAddressTensor, canonicalQ5Components,
      Q5CanonicalComponents.component] using
      canonicalAddressZBasis K (componentSpecAt i).address
  grade i := canonicalAddressZGrade K (componentSpecAt i).address

end MME.DWZFourthPrescribedZ181.OneHotActualCanonical


