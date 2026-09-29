-- Prove2me | solution 1 for mme_dwz_fourth_exact_scalar_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T08:23:06.600703+00:00
-- url     : https://prove2.me/submissions/a35d46ad-2ac7-48da-aebc-c315855a62bb

import Definitions.Def_mme_dwz_fourth_exact_scalar_certificate_data
import Theorems.Thm_mme_dwz_fourth_exact_retained_entropy_arithmetic
import Theorems.Thm_mme_dwz_fourth_log_lookup_sound

open MME MME.DWZFourthExactScalarCertificate
open MME
open MME.DWZFourthLogScaleTable
open MME.DWZFourthRetainedEntropy
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthRetainedEntropy

theorem exactRetainedEntropyArithmetic :
    checkRetainedEntropy = true :=
  mme_dwz_fourth_exact_retained_entropy_arithmetic

end MME.DWZFourthRetainedEntropy
namespace MME.DWZFourthLogScaleTable
open scoped Classical

theorem certificate_of_lookup :
    ∀ {index : Nat} {entry : Prod Rat Nat} (hlookup : entries[index]? = some entry),
    0 < entry.1 /\
      (MME.autoScaledLogLower entry.1 entry.2 6 : Real) <=
          Real.log (entry.1 : Real) /\
        Real.log (entry.1 : Real) <=
          (MME.autoScaledLogUpper entry.1 entry.2 6 : Real) :=
  mme_dwz_fourth_log_lookup_sound

end MME.DWZFourthLogScaleTable

namespace MME.DWZFourthExactScalarCertificate
open MME MME.DWZFourthLogScaleTable MME.DWZFourthRetainedEntropy

/-- `entropyEndpoint` with the table lookup as a parameter. -/
private def endpointWith (tbl : Nat → Option (Rat × Nat)) (useUpper : Bool) :
    List Nat → Option Rat
  | [] => some 0
  | logIndex :: tail => do
      let entry <- tbl logIndex
      let rest <- endpointWith tbl useUpper tail
      let logBound := if useUpper then
        MME.autoScaledLogLower entry.1 entry.2 6
      else
        MME.autoScaledLogUpper entry.1 entry.2 6
      pure (-(entry.1 * logBound) + rest)

private theorem endpoint_eq (useUpper : Bool) (cells : List Nat) :
    entropyEndpoint useUpper cells = endpointWith (fun i ↦ entries[i]?) useUpper cells := by
  induction cells with
  | nil => rfl
  | cons x t ih => simp only [entropyEndpoint, endpointWith, ih]

/-- `entropyEndpoint_sound` with the table as a variable.  Stated over the concrete `entries`, the
kernel must see through `match entries[x]?` for a variable `x`, which evaluates `entries.size`
and materializes the whole appended table (over 14 GB); here nothing concrete exists to reduce. -/
private theorem endpointWith_sound (tbl : Nat → Option (Rat × Nat))
    (htbl : ∀ {index : Nat} {entry : Rat × Nat}, tbl index = some entry →
      0 < entry.1 ∧
        (MME.autoScaledLogLower entry.1 entry.2 6 : ℝ) ≤ Real.log (entry.1 : ℝ) ∧
        Real.log (entry.1 : ℝ) ≤ (MME.autoScaledLogUpper entry.1 entry.2 6 : ℝ))
    (cells : List Nat) (lower upper : ℚ)
    (hlower : endpointWith tbl false cells = some lower)
    (hupper : endpointWith tbl true cells = some upper) :
    (lower : ℝ) ≤ entropyActualWith tbl cells ∧ entropyActualWith tbl cells ≤ (upper : ℝ) := by
  induction cells generalizing lower upper with
  | nil =>
      simp [endpointWith] at hlower hupper
      subst lower
      subst upper
      simp [entropyActualWith]
  | cons logIndex tail ih =>
      cases hentry : tbl logIndex with
      | none =>
          simp [endpointWith, hentry] at hlower
      | some entry =>
          cases hlowerTail : endpointWith tbl false tail with
          | none =>
              simp [endpointWith, hentry, hlowerTail] at hlower
          | some lowerTail =>
              cases hupperTail : endpointWith tbl true tail with
              | none =>
                  simp [endpointWith, hentry, hupperTail] at hupper
              | some upperTail =>
                  have hlowerEq :
                      -(entry.1 * autoScaledLogUpper entry.1 entry.2 6) +
                          lowerTail = lower := by
                    simpa [endpointWith, hentry, hlowerTail] using hlower
                  have hupperEq :
                      -(entry.1 * autoScaledLogLower entry.1 entry.2 6) +
                          upperTail = upper := by
                    simpa [endpointWith, hentry, hupperTail] using hupper
                  have hcertificate := htbl hentry
                  have hlog := hcertificate.2
                  have hq : (0 : ℝ) ≤ (entry.1 : ℝ) := by
                    exact_mod_cast hcertificate.1.le
                  have hcellLower :
                      ((-(entry.1 * autoScaledLogUpper entry.1 entry.2 6) : ℚ) : ℝ) ≤
                        Real.negMulLog (entry.1 : ℝ) := by
                    rw [Real.negMulLog_eq_neg]
                    push_cast
                    exact neg_le_neg
                      (mul_le_mul_of_nonneg_left hlog.2 hq)
                  have hcellUpper :
                      Real.negMulLog (entry.1 : ℝ) ≤
                        ((-(entry.1 * autoScaledLogLower entry.1 entry.2 6) : ℚ) : ℝ) := by
                    rw [Real.negMulLog_eq_neg]
                    push_cast
                    exact neg_le_neg
                      (mul_le_mul_of_nonneg_left hlog.1 hq)
                  have htail := ih lowerTail upperTail hlowerTail hupperTail
                  constructor
                  · rw [← hlowerEq]
                    push_cast
                    simp only [entropyActualWith, hentry]
                    exact add_le_add
                      (by
                        simpa only [Rat.cast_neg, Rat.cast_mul] using hcellLower)
                      htail.1
                  · rw [← hupperEq]
                    push_cast
                    simp only [entropyActualWith, hentry]
                    exact add_le_add
                      (by
                        simpa only [Rat.cast_neg, Rat.cast_mul] using hcellUpper)
                      htail.2

end MME.DWZFourthExactScalarCertificate

namespace MME.DWZFourthExactScalarCertificate

private theorem entropyEndpoint_sound (cells : List Nat) (lower upper : ℚ)
    (hlower : entropyEndpoint false cells = some lower)
    (hupper : entropyEndpoint true cells = some upper) :
    (lower : ℝ) ≤ entropyActual cells ∧ entropyActual cells ≤ (upper : ℝ) := by
  rw [endpoint_eq] at hlower hupper
  exact endpointWith_sound _ (fun h ↦ certificate_of_lookup h) cells lower upper hlower hupper

private theorem entropyRecord_sound (record : EntropyRecord)
    (hrecord : recordAccepts record = true) :
    (record.lowerFloor : ℝ) ≤ entropyActual record.cells ∧
      entropyActual record.cells ≤ (record.upperCeiling : ℝ) := by
  unfold recordAccepts at hrecord
  cases hlower : entropyEndpoint false record.cells with
  | none => simp [hlower] at hrecord
  | some lower =>
      cases hupper : entropyEndpoint true record.cells with
      | none => simp [hlower, hupper] at hrecord
      | some upper =>
          simp [hlower, hupper] at hrecord
          have hsound := entropyEndpoint_sound record.cells lower upper hlower hupper
          constructor
          · exact le_trans (by exact_mod_cast hrecord.1) hsound.1
          · exact le_trans hsound.2 (by exact_mod_cast hrecord.2)

private theorem allEntropyRecordsAccept :
    entropyRecords.all recordAccepts = true := by
  have h := exactRetainedEntropyArithmetic
  simp only [checkRetainedEntropy, Bool.and_eq_true] at h
  exact h.1

private theorem allRetainedEntropyRecordsSound (i : Fin entropyRecords.size) :
    ((entropyRecords[i]).lowerFloor : ℝ) ≤
        entropyActual (entropyRecords[i]).cells ∧
      entropyActual (entropyRecords[i]).cells ≤
        ((entropyRecords[i]).upperCeiling : ℝ) := by
  apply entropyRecord_sound
  exact (Array.all_eq_true.mp allEntropyRecordsAccept) i i.isLt

private theorem termValue_sound (term : EntropyTerm) (value : ℚ)
    (hsafe : termSafe term = true)
    (hvalue : termValue term = some value) :
    ∃ actual, termActual term = some actual ∧ (value : ℝ) ≤ actual := by
  cases hrecord : entropyRecords[term.recordIndex]? with
  | none => simp [termValue, hrecord] at hvalue
  | some record =>
      obtain ⟨hindex, hget⟩ := Array.getElem?_eq_some_iff.mp hrecord
      have hacceptAt : recordAccepts entropyRecords[term.recordIndex] = true :=
        (Array.all_eq_true.mp allEntropyRecordsAccept) term.recordIndex hindex
      have haccept : recordAccepts record = true := by
        simpa only [hget] using hacceptAt
      have hsound := entropyRecord_sound record haccept
      cases hupper : term.useUpper with
      | false =>
          simp [termValue, hrecord, hupper] at hvalue
          subst value
          refine ⟨(term.coefficient : ℝ) * entropyActual record.cells, ?_, ?_⟩
          · simp [termActual, hrecord]
          · have hcoefficient : (0 : ℝ) ≤ (term.coefficient : ℝ) := by
              unfold termSafe at hsafe
              simp [hupper] at hsafe
              exact_mod_cast hsafe
            push_cast
            exact mul_le_mul_of_nonneg_left hsound.1 hcoefficient
      | true =>
          simp [termValue, hrecord, hupper] at hvalue
          subst value
          refine ⟨(term.coefficient : ℝ) * entropyActual record.cells, ?_, ?_⟩
          · simp [termActual, hrecord]
          · have hcoefficient : (term.coefficient : ℝ) ≤ 0 := by
              unfold termSafe at hsafe
              simp [hupper] at hsafe
              exact_mod_cast hsafe
            push_cast
            exact mul_le_mul_of_nonpos_left hsound.2 hcoefficient

private theorem termsValue_sound (terms : List EntropyTerm) (value : ℚ)
    (hsafe : terms.all termSafe = true)
    (hvalue : termsValue terms = some value) :
    ∃ actual, termsActual terms = some actual ∧ (value : ℝ) ≤ actual := by
  induction terms generalizing value with
  | nil =>
      simp [termsValue] at hvalue
      subst value
      exact ⟨0, by simp [termsActual], by norm_num⟩
  | cons term tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hsafe
      cases htermValue : termValue term with
      | none => simp [termsValue, htermValue] at hvalue
      | some termBound =>
          cases htailValue : termsValue tail with
          | none => simp [termsValue, htermValue, htailValue] at hvalue
          | some tailBound =>
              simp [termsValue, htermValue, htailValue] at hvalue
              subst value
              obtain ⟨termReal, htermReal, htermSound⟩ :=
                termValue_sound term termBound hsafe.1 htermValue
              obtain ⟨tailReal, htailReal, htailSound⟩ :=
                ih tailBound hsafe.2 htailValue
              refine ⟨termReal + tailReal, ?_, ?_⟩
              · simp [termsActual, htermReal, htailReal]
              · push_cast
                exact add_le_add htermSound htailSound

private theorem allRetainedObligationsAccept :
    obligations.all branchAccepts = true := by
  have h := exactRetainedEntropyArithmetic
  simp only [checkRetainedEntropy, Bool.and_eq_true] at h
  exact h.2

private theorem branch_sound (branch : FloorBranch)
    (hbranch : branchAccepts branch = true) :
    ∃ actual, termsActual branch.terms = some actual ∧
      (branch.retainedFloor : ℝ) ≤ (branch.constant : ℝ) + actual := by
  unfold branchAccepts at hbranch
  have hparts := Bool.and_eq_true_iff.mp hbranch
  have hsafe := hparts.1
  have hbound := hparts.2
  cases hvalue : termsValue branch.terms with
  | none => simp [hvalue] at hbound
  | some value =>
      simp only [hvalue] at hbound
      have hrational : branch.retainedFloor ≤ branch.constant + value :=
        of_decide_eq_true hbound
      obtain ⟨actual, hactual, hsound⟩ :=
        termsValue_sound branch.terms value hsafe hvalue
      refine ⟨actual, hactual, ?_⟩
      calc
        (branch.retainedFloor : ℝ) ≤
            ((branch.constant + value : ℚ) : ℝ) := by
          exact_mod_cast hrational
        _ = (branch.constant : ℝ) + (value : ℝ) := by push_cast; rfl
        _ ≤ (branch.constant : ℝ) + actual :=
          add_le_add (le_refl _) hsound

private theorem allRetainedBranchesSound (i : Fin obligations.size) :
    ∃ actual, termsActual (obligations[i]).terms = some actual ∧
      ((obligations[i]).retainedFloor : ℝ) ≤
        ((obligations[i]).constant : ℝ) + actual := by
  apply branch_sound
  exact (Array.all_eq_true.mp allRetainedObligationsAccept) i i.isLt

end MME.DWZFourthExactScalarCertificate

theorem solution :
    (∀ (i : Fin entropyRecords.size),
      ((entropyRecords[i]).lowerFloor : ℝ) ≤
          entropyActual (entropyRecords[i]).cells ∧
        entropyActual (entropyRecords[i]).cells ≤
          ((entropyRecords[i]).upperCeiling : ℝ)) ∧
    (∀ (i : Fin obligations.size),
      ∃ actual, termsActual (obligations[i]).terms = some actual ∧
        ((obligations[i]).retainedFloor : ℝ) ≤
          ((obligations[i]).constant : ℝ) + actual) :=
  ⟨allRetainedEntropyRecordsSound, allRetainedBranchesSound⟩
