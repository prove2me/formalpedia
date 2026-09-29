-- Prove2me | solution 1 for mme_dwz_fourth_tensor_ledger_metadata
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:03:32.747522+00:00
-- url     : https://prove2.me/submissions/bd950934-9856-4f31-ba4b-278abd449c55

import Definitions.Def_mme_dwz_fourth_tensor_ledger_metadata_data
import Theorems.Thm_mme_dwz_fourth_scalar_ledger_induction_facade

open MME MME.DWZFourthTensorLedger MME.DWZFourthTensorLedger.Q5CanonicalComponents
open MME
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

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

private theorem componentSpecAt_valid (index : Fin 180) :
    (componentSpecAt index).valid = true := by
  decide +kernel +revert

private theorem componentObjectIds_nodup : componentObjectIds.Nodup := by
  decide +kernel

private theorem ledgerObjectId_final :
    ledgerObjectId ⟨180, by norm_num⟩ = 184 := by
  decide +kernel

/-- Exactly six base profiles, 129 reachable square profiles, and all
45 fourth-power block profiles occur in the 180 component entries. -/
private theorem componentLayerCounts :
    (componentMetadata.toList.filter fun m =>
      match m.address with | .base .. => true | _ => false).length = 6 ∧
    (componentMetadata.toList.filter fun m =>
      match m.address with | .square .. => true | _ => false).length = 129 ∧
    (componentMetadata.toList.filter fun m =>
      match m.address with | .fourth .. => true | _ => false).length = 45 := by
  decide +kernel

namespace Q5CanonicalComponents

variable {K : Type u} [Field K]

end Q5CanonicalComponents

private theorem tensorAt_component {K : Type u} [Field K]
    (api : Q5CanonicalComponents K) (index : Fin 180) :
    tensorAt api (componentLedgerIndex index) =
      api.component (componentSpecAt index).address := by
  simp [tensorAt, componentLedgerIndex, index.isLt]

/-- Exact final-node identification.  After the public substitutions
`api.kron := TensorObj.kron` and `api.cwObj5 := CWObj K 5`, the right
side unfolds definitionally to `StothersFourth.cwFourthObj K 5`. -/
private theorem tensorAt_final_eq_cwFourthObj5 {K : Type u} [Field K]
    (api : Q5CanonicalComponents K) :
    tensorAt api ⟨180, by norm_num⟩ = api.cwFourthObj5 := by
  simp [tensorAt]

/-- End-to-end fourth-power conclusion with all 180 component/profile
addresses fixed by the extracted certificate.  The only remaining
premise is the tensor extraction law over this concrete family. -/
private theorem exactLedgerQ5FourthValue
    {K : Type u} [Field K]
    (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop)
    (api : Q5CanonicalComponents K) (tau : ℝ)
    (hmono : ∀ T A B, 0 ≤ A → A ≤ B →
      SixValueAtLeast T tau B → SixValueAtLeast T tau A)
    (hextraction : TensorRecursiveExtraction
      SixValueAtLeast (tensorAt api) tau) :
    SixValueAtLeast api.cwFourthObj5 tau (240101 / 100 : ℝ) := by
  rw [← tensorAt_final_eq_cwFourthObj5 api]
  exact exactLedgerTensorFamilyFourthValue
    SixValueAtLeast (tensorAt api) tau hmono hextraction

/-- Signature-faithful public-object wrapper.  In a full checkout take
`stothersFourthObj5 := StothersFourth.cwFourthObj K 5`; the displayed
equality is then `rfl` for the canonical API. -/
private theorem exactLedgerQ5StothersFourthValue
    {K : Type u} [Field K]
    (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop)
    (api : Q5CanonicalComponents K)
    (stothersFourthObj5 : TensorObj K 3)
    (hpublic : stothersFourthObj5 = api.cwFourthObj5)
    (tau : ℝ)
    (hmono : ∀ T A B, 0 ≤ A → A ≤ B →
      SixValueAtLeast T tau B → SixValueAtLeast T tau A)
    (hextraction : TensorRecursiveExtraction
      SixValueAtLeast (tensorAt api) tau) :
    SixValueAtLeast stothersFourthObj5 tau (240101 / 100 : ℝ) := by
  rw [hpublic]
  exact exactLedgerQ5FourthValue
    SixValueAtLeast api tau hmono hextraction

end MME.DWZFourthTensorLedger

theorem solution :
    (∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K) (index : Fin 180),
      tensorAt api (componentLedgerIndex index) =
        api.component (componentSpecAt index).address) ∧
    (∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K),
      tensorAt api ⟨180, by norm_num⟩ = api.cwFourthObj5) :=
  ⟨tensorAt_component, tensorAt_final_eq_cwFourthObj5⟩
