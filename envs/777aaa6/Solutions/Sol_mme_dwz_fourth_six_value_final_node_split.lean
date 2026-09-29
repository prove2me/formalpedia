-- Prove2me | solution 1 for mme_dwz_fourth_six_value_final_node_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:01:20.592149+00:00
-- url     : https://prove2.me/submissions/696291ed-ea12-4fbb-871c-3cf0ac91880a

import Definitions.Def_mme_dwz_fourth_six_value_final_node_split_data
import Theorems.Thm_mme_dwz_fourth_scalar_ledger_induction_facade

open MME MME.DWZFourthSixFinalSplit
open MME
open MME.DWZFourthScalarLedger
open MME.DWZFourthScalarLedgerInduction
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
namespace MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

theorem fourth_value_exceeds_2401_01_of_natural_rate_floor :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate :=
  mme_dwz_fourth_terminal_log_margin

end MME.DWZFourthScalar

namespace MME.DWZFourthSixFinalSplit

private theorem globalLedgerNode_accepts :
    nodeAccepts properLedgerRates globalLedgerNode = true := by
  decide +kernel

private theorem globalLedgerNode_rateFloor :
    globalLedgerNode.rateFloor = finalRateFloor := by
  decide +kernel

private theorem properSixEndpoints_of_pointwise
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hpointwise : ProperSixEndpointsPointwise tensorAt tau) :
    ProperSixEndpoints tensorAt tau := by
  intro index rate hlookup
  have hindex : index < properLedgerRates.size :=
    (Array.getElem?_eq_some_iff.mp hlookup).choose
  have hindex180 : index < 180 := by
    simpa [properLedgerRates_size] using hindex
  let i : Fin 180 := ⟨index, hindex180⟩
  have hi := hpointwise i
  have hrate : properLedgerRate i = rate := by
    have := (Array.getElem?_eq_some_iff.mp hlookup).choose_spec
    simpa [properLedgerRate, i] using this
  subst rate
  simpa [tensorAtNat, properLedgerIndex, i, Nat.mod_eq_of_lt
    (Nat.lt_trans hindex180 (by norm_num : 180 < 181))] using hi

private theorem hasSix_mono_endpoint
    {K : Type u} [Field K] {T : TensorObj K 3}
    (tau A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : HasSixSymmetricTauValueAtLeast T tau B) :
    HasSixSymmetricTauValueAtLeast T tau A := by
  unfold HasSixSymmetricTauValueAtLeast at hB ⊢
  rcases hB with ⟨hB0, hB⟩
  refine ⟨pow_nonneg hA 6, ?_⟩
  intro epsilon hepsilon
  exact (hB epsilon hepsilon).mono (fun N hN ↦ by
    rcases hN with ⟨k, a, b, c, hrestrict, hweight⟩
    refine ⟨k, a, b, c, hrestrict, ?_⟩
    by_cases hepsilonOne : epsilon ≤ 1
    · have hpow : (A ^ 6) ^ N ≤ (B ^ 6) ^ N :=
        pow_le_pow_left₀ (pow_nonneg hA 6)
          (pow_le_pow_left₀ hA hAB 6) N
      exact (mul_le_mul_of_nonneg_right hpow
        (sub_nonneg.mpr hepsilonOne)).trans hweight
    · have hleft : (A ^ 6) ^ N * (1 - epsilon) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (pow_nonneg hA 6) N)
          (sub_nonpos.mpr (le_of_not_ge hepsilonOne))
      exact hleft.trans (Finset.sum_nonneg
        (fun i _ ↦ Real.rpow_nonneg (by positivity) tau)))

/-- Once the 180 ordinary component endpoints are loaded, the checked scalar
ledger and one final extraction imply the target fourth-power value. -/
private theorem headline
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hproper : ProperSixEndpoints tensorAt tau)
    (hglobal : FinalSixExtraction tensorAt tau) :
    HasSixSymmetricTauValueAtLeast
      (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ) := by
  obtain ⟨hnonnegative, weighted, hweighted, hbound⟩ :=
    nodeAccepts_facts properLedgerRates globalLedgerNode
      globalLedgerNode_accepts
  have hproduct := weightedValueProduct_eq_exp
    properLedgerRates globalLedgerNode.children weighted hweighted
  have hchildren := childrenRealize_of_weightedPrior
    (fun index value ↦
      HasSixSymmetricTauValueAtLeast
        (tensorAtNat tensorAt index) tau value)
    properLedgerRates globalLedgerNode weighted hweighted hproper
  have hlarge := hglobal weighted (Real.exp (weighted : ℝ))
    hnonnegative hweighted hproduct hchildren
  have hnode : HasSixSymmetricTauValueAtLeast
      (tensorAtNat tensorAt properLedgerRates.size) tau
      (Real.exp (globalLedgerNode.rateFloor : ℝ)) :=
    hasSix_mono_endpoint tau
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
  have hsmall := hasSix_mono_endpoint tau
    (240101 / 100 : ℝ) (Real.exp (finalRateFloor : ℝ))
    (by norm_num) htarget.le hnode
  simpa [tensorAtNat] using hsmall

end MME.DWZFourthSixFinalSplit

theorem solution :
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpointwise : ProperSixEndpointsPointwise tensorAt tau),
      ProperSixEndpoints tensorAt tau) ∧
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hproper : ProperSixEndpoints tensorAt tau) (hglobal : FinalSixExtraction tensorAt tau),
      HasSixSymmetricTauValueAtLeast
        (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ)) :=
  ⟨properSixEndpoints_of_pointwise, headline⟩
