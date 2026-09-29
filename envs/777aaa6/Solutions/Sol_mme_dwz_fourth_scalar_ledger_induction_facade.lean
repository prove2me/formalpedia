-- Prove2me | solution 1 for mme_dwz_fourth_scalar_ledger_induction_facade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T04:59:10.609351+00:00
-- url     : https://prove2.me/submissions/e3c813aa-f65e-4737-8526-c40a3485b915

import Definitions.Def_mme_dwz_fourth_scalar_ledger_induction_facade_data
import Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin

open MME MME.DWZFourthScalarLedgerInduction
open MME.DWZFourthScalarLedger
open MME
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
namespace MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

theorem fourth_value_exceeds_2401_01_of_natural_rate_floor :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate :=
  mme_dwz_fourth_terminal_log_margin

end MME.DWZFourthScalar

namespace MME.DWZFourthScalarLedgerInduction

private theorem rateRealizes_push
    (ValueAtLeast : Nat → ℝ → Prop) (prior : Array Rat)
    (rate : Rat)
    (hprior : RateRealizes ValueAtLeast prior)
    (hnew : ValueAtLeast prior.size (Real.exp (rate : ℝ))) :
    RateRealizes ValueAtLeast (prior.push rate) := by
  unfold RateRealizes at hprior ⊢
  intro index stored hlookup
  rw [Array.getElem?_push] at hlookup
  split at hlookup
  · rename_i hindex
    have hrate : rate = stored := Option.some.inj hlookup
    subst index
    subst stored
    exact hnew
  · exact hprior index stored hlookup

private theorem nodeAccepts_facts (prior : Array Rat) (node : Node)
    (hnode : nodeAccepts prior node = true) :
    (∀ term ∈ node.children, 0 ≤ term.2) ∧
      ∃ weighted,
        weightedPrior prior node.children = some weighted ∧
          node.rateFloor ≤ weighted + node.retainedFloor := by
  unfold nodeAccepts at hnode
  have hparts := Bool.and_eq_true_iff.mp hnode
  have hnonnegative := hparts.1
  simp only [List.all_eq_true, decide_eq_true_eq] at hnonnegative
  cases hweighted : weightedPrior prior node.children with
  | none => simp [hweighted] at hparts
  | some weighted =>
      have hbound := hparts.2
      simp only [hweighted] at hbound
      exact ⟨hnonnegative, weighted, rfl, of_decide_eq_true hbound⟩

private theorem checkAux_realizes
    (ValueAtLeast : Nat → ℝ → Prop)
    (hclosure : NodeClosure ValueAtLeast)
    (nodes : List Node) (prior : Array Rat)
    (hprior : RateRealizes ValueAtLeast prior)
    (hcheck : checkAux nodes prior = true) :
    RateRealizes ValueAtLeast (runRates nodes prior) := by
  induction nodes generalizing prior with
  | nil => simpa [runRates] using hprior
  | cons node tail ih =>
      simp only [checkAux, Bool.and_eq_true] at hcheck
      obtain ⟨hnonnegative, weighted, hweighted, hbound⟩ :=
        nodeAccepts_facts prior node hcheck.1
      have hnew :
          ValueAtLeast prior.size (Real.exp (node.rateFloor : ℝ)) := by
        exact hclosure prior node weighted hnonnegative hweighted hbound hprior
      exact ih (prior.push node.rateFloor)
        (rateRealizes_push ValueAtLeast prior node.rateFloor hprior hnew)
        hcheck.2

private theorem exactRates_size : exactRates.size = 181 := by
  decide +kernel

private theorem finalRateFloor_lookup :
    exactRates[180]? = some finalRateFloor := by
  decide +kernel

private theorem exactLedgerRealizes
    (ValueAtLeast : Nat → ℝ → Prop)
    (hclosure : NodeClosure ValueAtLeast) :
    RateRealizes ValueAtLeast exactRates := by
  apply checkAux_realizes ValueAtLeast hclosure ledger #[]
  · unfold RateRealizes
    intro index rate hlookup
    simp at hlookup
  · exact exactRationalRecurrenceCertificate.1

/-- The 181st (zero-based index 180) ledger component inherits the exact
certified endpoint once the tensor-specific one-node closure is supplied. -/
private theorem exactLedgerFinalComponentValue
    (ValueAtLeast : Nat → ℝ → Prop)
    (hclosure : NodeClosure ValueAtLeast) :
    ValueAtLeast 180 (Real.exp (finalRateFloor : ℝ)) := by
  have hrealizes := exactLedgerRealizes ValueAtLeast hclosure
  exact hrealizes 180 finalRateFloor finalRateFloor_lookup

/-- Monotonicity converts the exact endpoint into the conservative natural
rate floor used by the fourth-power target. -/
private theorem exactLedgerNaturalFloorComponentValue
    (ValueAtLeast : Nat → ℝ → Prop)
    (hmono : ∀ index A B, 0 ≤ A → A ≤ B →
      ValueAtLeast index B → ValueAtLeast index A)
    (hclosure : NodeClosure ValueAtLeast) :
    ValueAtLeast 180 (Real.exp (naturalRateFloor : ℝ)) := by
  apply hmono 180 (Real.exp (naturalRateFloor : ℝ))
    (Real.exp (finalRateFloor : ℝ)) (Real.exp_pos _).le
    (Real.exp_le_exp.mpr exactRationalRecurrenceCertificateReal)
  exact exactLedgerFinalComponentValue ValueAtLeast hclosure

/-- Final abstract tensor-value facade at the requested fourth-power value.
No scalar premise remains: the only hypothesis is the reusable one-node
tensor closure plus ordinary downward monotonicity of the value predicate. -/
private theorem exactLedgerFourthValueExceeds2401_01
    (ValueAtLeast : Nat → ℝ → Prop)
    (hmono : ∀ index A B, 0 ≤ A → A ≤ B →
      ValueAtLeast index B → ValueAtLeast index A)
    (hclosure : NodeClosure ValueAtLeast) :
    ValueAtLeast 180 (240101 / 100 : ℝ) := by
  have htarget : (240101 / 100 : ℝ) <
      Real.exp (finalRateFloor : ℝ) := by
    apply MME.DWZFourthScalar.fourth_value_exceeds_2401_01_of_natural_rate_floor
    simpa [MME.DWZFourthScalar.naturalRateFloor, naturalRateFloor] using
      exactRationalRecurrenceCertificateReal
  apply hmono 180 (240101 / 100 : ℝ)
    (Real.exp (finalRateFloor : ℝ)) (by norm_num) htarget.le
  exact exactLedgerFinalComponentValue ValueAtLeast hclosure

section TensorFamily

private theorem weightedValueProduct_eq_exp
    (prior : Array Rat) (terms : List (Prod Nat Rat)) (weighted : Rat)
    (hweighted : weightedPrior prior terms = some weighted) :
    weightedValueProduct prior terms = some (Real.exp (weighted : ℝ)) := by
  induction terms generalizing weighted with
  | nil =>
      simp [weightedPrior] at hweighted
      subst weighted
      simp [weightedValueProduct]
  | cons term tail ih =>
      cases hrate : prior[term.1]? with
      | none => simp [weightedPrior, hrate] at hweighted
      | some rate =>
          cases htail : weightedPrior prior tail with
          | none => simp [weightedPrior, hrate, htail] at hweighted
          | some tailWeighted =>
              simp [weightedPrior, hrate, htail] at hweighted
              subst weighted
              have htailProduct := ih tailWeighted htail
              simp [weightedValueProduct, hrate, htailProduct]
              rw [← Real.exp_mul, ← Real.exp_add]
              congr 1
              ring

private theorem weightedPrior_lookup_of_mem
    (prior : Array Rat) (terms : List (Prod Nat Rat))
    (weighted : Rat) (term : Prod Nat Rat)
    (hweighted : weightedPrior prior terms = some weighted)
    (hterm : term ∈ terms) :
    ∃ rate, prior[term.1]? = some rate := by
  induction terms generalizing weighted with
  | nil => simp at hterm
  | cons head tail ih =>
      cases hrate : prior[head.1]? with
      | none => simp [weightedPrior, hrate] at hweighted
      | some rate =>
          cases htail : weightedPrior prior tail with
          | none => simp [weightedPrior, hrate, htail] at hweighted
          | some tailWeighted =>
              simp only [List.mem_cons] at hterm
              rcases hterm with hhead | htailMem
              · subst term
                exact ⟨rate, hrate⟩
              · exact ih tailWeighted htail htailMem

private theorem childrenRealize_of_weightedPrior
    (ValueAtLeast : Nat → ℝ → Prop)
    (prior : Array Rat) (node : Node) (weighted : Rat)
    (hweighted : weightedPrior prior node.children = some weighted)
    (hprior : RateRealizes ValueAtLeast prior) :
    ChildrenRealize ValueAtLeast prior node := by
  intro term hterm
  obtain ⟨rate, hrate⟩ := weightedPrior_lookup_of_mem
    prior node.children weighted term hweighted hterm
  exact ⟨rate, hrate, hprior term.1 rate hrate⟩

private theorem exp_rateFloor_le_weighted_product
    (node : Node) (weighted : Rat)
    (hbound : node.rateFloor ≤ weighted + node.retainedFloor) :
    Real.exp (node.rateFloor : ℝ) ≤
      Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ) := by
  have hboundReal : (node.rateFloor : ℝ) ≤
      (weighted : ℝ) + (node.retainedFloor : ℝ) := by
    exact_mod_cast hbound
  calc
    Real.exp (node.rateFloor : ℝ) ≤
        Real.exp ((weighted : ℝ) + (node.retainedFloor : ℝ)) :=
      Real.exp_le_exp.mpr hboundReal
    _ = Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ) := by
      rw [Real.exp_add]
      ring

private theorem nodeClosure_of_tensorRecursiveExtraction
    {K : Type u} [Field K]
    (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop)
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hmono : ∀ T A B, 0 ≤ A → A ≤ B →
      SixValueAtLeast T tau B → SixValueAtLeast T tau A)
    (hextraction : TensorRecursiveExtraction SixValueAtLeast tensorAt tau) :
    NodeClosure
      (fun index value =>
        SixValueAtLeast (tensorAtNat tensorAt index) tau value) := by
  intro prior node weighted hnonnegative hweighted hbound hprior
  have hproduct := weightedValueProduct_eq_exp
    prior node.children weighted hweighted
  have hchildren := childrenRealize_of_weightedPrior
    (fun index value =>
      SixValueAtLeast (tensorAtNat tensorAt index) tau value)
    prior node weighted hweighted hprior
  have hlarge := hextraction prior node weighted
    (Real.exp (weighted : ℝ)) hnonnegative hweighted hproduct hchildren
  exact hmono (tensorAtNat tensorAt prior.size)
    (Real.exp (node.rateFloor : ℝ))
    (Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ))
    (Real.exp_pos _).le (exp_rateFloor_le_weighted_product node weighted hbound)
    hlarge

/-- Instantiation of the 181-node scalar replay for an abstract prescribed-Z
or six-symmetric tensor-value predicate.  The conclusion is the requested
fourth-power value; the only mathematical premise left is the per-node
finite tensor extraction interface. -/
private theorem exactLedgerTensorFamilyFourthValue
    {K : Type u} [Field K]
    (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop)
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ)
    (hmono : ∀ T A B, 0 ≤ A → A ≤ B →
      SixValueAtLeast T tau B → SixValueAtLeast T tau A)
    (hextraction : TensorRecursiveExtraction SixValueAtLeast tensorAt tau) :
    SixValueAtLeast (tensorAt ⟨180, by norm_num⟩) tau
      (240101 / 100 : ℝ) := by
  have hresult := exactLedgerFourthValueExceeds2401_01
    (fun index value =>
      SixValueAtLeast (tensorAtNat tensorAt index) tau value)
    (fun index A B hA hAB =>
      hmono (tensorAtNat tensorAt index) A B hA hAB)
    (nodeClosure_of_tensorRecursiveExtraction
      SixValueAtLeast tensorAt tau hmono hextraction)
  simpa [tensorAtNat] using hresult

end TensorFamily

end MME.DWZFourthScalarLedgerInduction

theorem solution :
    (∀ (prior : Array Rat) (node : Node) (hnode : nodeAccepts prior node = true),
      (∀ term ∈ node.children, 0 ≤ term.2) ∧
        ∃ weighted,
          weightedPrior prior node.children = some weighted ∧
            node.rateFloor ≤ weighted + node.retainedFloor) ∧
    (∀ (ValueAtLeast : Nat → ℝ → Prop) (hclosure : NodeClosure ValueAtLeast),
      ValueAtLeast 180 (Real.exp (finalRateFloor : ℝ))) ∧
    (∀ (prior : Array Rat) (terms : List (Prod Nat Rat)) (weighted : Rat) (hweighted : weightedPrior prior terms = some weighted),
      weightedValueProduct prior terms = some (Real.exp (weighted : ℝ))) ∧
    (∀ (ValueAtLeast : Nat → ℝ → Prop) (prior : Array Rat) (node : Node) (weighted : Rat) (hweighted : weightedPrior prior node.children = some weighted) (hprior : RateRealizes ValueAtLeast prior),
      ChildrenRealize ValueAtLeast prior node) ∧
    (∀ (node : Node) (weighted : Rat) (hbound : node.rateFloor ≤ weighted + node.retainedFloor),
      Real.exp (node.rateFloor : ℝ) ≤
        Real.exp (node.retainedFloor : ℝ) * Real.exp (weighted : ℝ)) ∧
    (∀ {K : Type u} [Field K] (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop) (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hmono : ∀ T A B, 0 ≤ A → A ≤ B → SixValueAtLeast T tau B → SixValueAtLeast T tau A) (hextraction : TensorRecursiveExtraction SixValueAtLeast tensorAt tau),
      SixValueAtLeast (tensorAt ⟨180, by norm_num⟩) tau
        (240101 / 100 : ℝ)) :=
  ⟨nodeAccepts_facts, exactLedgerFinalComponentValue, weightedValueProduct_eq_exp, childrenRealize_of_weightedPrior, exp_rateFloor_le_weighted_product, exactLedgerTensorFamilyFourthValue⟩
