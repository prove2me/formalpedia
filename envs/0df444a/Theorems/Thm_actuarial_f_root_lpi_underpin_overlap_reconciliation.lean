-- Prove2me | Theorems.Thm_actuarial_f_root_lpi_underpin_overlap_reconciliation
-- name    : actuarial_f_root_lpi_underpin_overlap_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:39:12.761488+00:00
-- url     : https://prove2.me/theorems/b12cea45-ff44-4f4c-bb33-865ebd045ffc
-- title:
--   Conditional anti-franking, statutory GMP and protected survivor reconciliation
-- statement:
--   Integrated monthly cashflow and survivor replacement valuation. Date indices now follow a fixed-anchor monthly calendar, and survivor anti-franking is assessed using a certified death date between the final alive payment and the next payment. Conditional section 87 pension floors exclude both historical employment cases, remove certified pre-1985 transfer-credit growth and include section 90 additions only when post-cessation employment accrual is eligible. Full statutory determinations, source-member data and all other section 87-92 exceptions require independent legal review. The root remains an unproved Lean obligation. The survivor GMP increase timetable starts from a separately certified valid GMP payable date no earlier than actual member death. No GMP is paid in this model before that date.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_fixedChoicePayment
import Definitions.Def_actuarial_f_monthlyScheduledGrowth
import Definitions.Def_actuarial_f_gmpValidYYYYMMDD
import Definitions.Def_actuarial_f_gmpDaysInMonth
import Definitions.Def_actuarial_f_gmpBoundedMemberMinimum
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth
import Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
import Definitions.Def_actuarial_f_gmpProtectedDirectEPV
import Definitions.Def_actuarial_f_gmpProtectedStateEPV
import Definitions.Def_actuarial_f_gmpProtectedReplacementEPV
import Definitions.Def_actuarial_f_gmpProtectedDisplaceableEPV
import Definitions.Def_actuarial_f_afLaterEarningsAddition
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afMemberSection87TopUp
import Definitions.Def_actuarial_f_afSurvivorCombinedMinimum

open ActuarialUnderpinsF

theorem actuarial_f_root_lpi_underpin_overlap_reconciliation
    (n h retirement guarantee firstA firstB firstC : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c estate : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ)
    (inflationA inflationB inflationC inflationS : ℕ → ℝ)
    (survivorFirst : ℕ → ℕ) (ge : ℕ → ℝ)
    (floorA capA floorB capB floorC capC floorS capS : ℝ)
    (dateOf : ℕ → ℕ) (memberDeathDate : ℕ → ℕ → ℕ)
    (gmpPayableDate cessationDate : ℕ)
    (pre88Gmp post88Gmp : ℕ → ℝ)
    (survivorPre88 survivorPost88 : ℕ → ℕ → ℝ)
    (survivorGmpEligible : ℕ → ℕ → Bool)
    (survivorGmpPayableDate : ℕ → ℕ → ℕ)
    (gmpAnnualOrderRate : ℕ → ℝ)
    (memberLeftBefore1985 memberContractingOutEndedBefore1985
       memberFullEntitlement memberCompleteSubstitute
       memberLaterAccrualApplies : ℕ → Bool)
    (memberRelevantWeekly memberGmpAtCessationWeekly
       memberAppropriateWeekly memberAssumedLaterWeekly : ℕ → ℝ)
    (survivorFullEntitlement survivorCompleteSubstitute
       survivorLaterAccrualApplies : ℕ → ℕ → Bool)
    (survivorRelevantWeekly survivorAppropriateWeekly
       survivorAssumedLaterWeekly survivorExcludedTransferGrowth : ℕ → ℕ → ℝ)
    (memberExcludedTransferGrowth : ℕ → ℝ)
    (hv : 0 < n ∧
      (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
        ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧
      (∑ z ∈ Finset.range n, ∑ i ∈ Finset.range (h + 1),
        ∑ j ∈ Finset.range (h + 1), p z i j) = 1)
    (hr : retirement ≤ h)
    (ha : retirement < firstA ∧ firstA ≤ retirement + 12)
    (hb : retirement < firstB ∧ firstB ≤ retirement + 12)
    (hc : retirement < firstC ∧ firstC ≤ retirement + 12)
    (hs : ∀ i ∈ Finset.range h,
      i + 1 < survivorFirst i ∧ survivorFirst i ≤ i + 13)
    (hfa : 0 ≤ floorA ∧ floorA ≤ capA)
    (hfb : 0 ≤ floorB ∧ floorB ≤ capB)
    (hfc : 0 ≤ floorC ∧ floorC ≤ capC)
    (hfs : 0 ≤ floorS ∧ floorS ≤ capS)
    (hdate : ∀ t ≤ h + 1, gmpValidYYYYMMDD (dateOf t))
    (hdateMono : ∀ t < h + 1, dateOf t < dateOf (t + 1))
    (hcalendar : ∀ t < h,
      let y := dateOf t / 10000
      let m := dateOf t % 10000 / 100
      let nextY := if m = 12 then y + 1 else y
      let nextM := if m = 12 then 1 else m + 1
      dateOf (t + 1) =
        nextY * 10000 + nextM * 100 +
          min (dateOf 0 % 100) (gmpDaysInMonth nextY nextM))
    (hdeath : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range h,
      gmpValidYYYYMMDD (memberDeathDate z i) ∧
      dateOf i ≤ memberDeathDate z i ∧
      memberDeathDate z i < dateOf (i + 1))
    (hSurvivorGmpDate : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range h,
      gmpValidYYYYMMDD (survivorGmpPayableDate z i) ∧
      memberDeathDate z i ≤ survivorGmpPayableDate z i)
    (htransferM : ∀ z ∈ Finset.range n, 0 ≤ memberExcludedTransferGrowth z)
    (htransferS : ∀ z ∈ Finset.range n,
      ∀ i ∈ Finset.range h, 0 ≤ survivorExcludedTransferGrowth z i) :
    let ga : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstA floorA capA inflationA t
    let gb : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstB floorB capB inflationB t
    let gc : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstC floorC capC inflationC t
    let gs : ℕ → ℕ → ℝ := fun i t =>
      monthlyScheduledGrowth (i + 1) (survivorFirst i)
        floorS capS inflationS t
    let memberStatutoryWeekly : ℕ → ℕ → ℝ := fun z t =>
      let gmpWeekly :=
        gmpBoundedMemberMinimum (pre88Gmp z) (post88Gmp z)
          gmpPayableDate (dateOf t) gmpAnnualOrderRate * 12 / 52
      let antifrankWeekly :=
        afMemberSection87WeeklyFloor cessationDate gmpPayableDate
          (dateOf t) (memberLeftBefore1985 z) (memberContractingOutEndedBefore1985 z)
          (memberFullEntitlement z) (memberCompleteSubstitute z)
          (memberLaterAccrualApplies z) (memberRelevantWeekly z) gmpWeekly
          (memberGmpAtCessationWeekly z) (memberAppropriateWeekly z)
          (afLaterEarningsAddition (memberRelevantWeekly z)
            (memberGmpAtCessationWeekly z) (memberAssumedLaterWeekly z))
          (memberExcludedTransferGrowth z)
      max gmpWeekly antifrankWeekly
    let memberSupplement : ℕ → ℕ → ℕ → ℝ := fun z i t =>
      if gmpPayableDate ≤ dateOf t then
        afMemberSection87TopUp retirement i t
          (fixedChoicePayment a b ga gb z t + c z * gc t)
          (memberStatutoryWeekly z t)
      else 0
    let survivorMinimum : ℕ → ℕ → ℕ → ℕ → ℝ := fun z i j t =>
      if spouseDue h i j t = 1 then
        let gmpMonthly :=
          if survivorGmpEligible z i = true ∧
              survivorGmpPayableDate z i ≤ dateOf t then
            max 0 (survivorPre88 z i +
              survivorPost88 z i *
                gmpBoundedPost88Growth (survivorGmpPayableDate z i)
                  (dateOf t) gmpAnnualOrderRate)
          else 0
        let antifrankWeekly :=
          afSurvivorSection87WeeklyFloor cessationDate (memberDeathDate z i)
            gmpPayableDate (dateOf t) (memberLeftBefore1985 z) (memberContractingOutEndedBefore1985 z)
            (survivorFullEntitlement z i) (survivorCompleteSubstitute z i)
            (survivorLaterAccrualApplies z i)
            (survivorRelevantWeekly z i) (gmpMonthly * 12 / 52)
            (memberGmpAtCessationWeekly z) (survivorAppropriateWeekly z i)
            (afLaterEarningsAddition (survivorRelevantWeekly z i)
              (memberGmpAtCessationWeekly z / 2)
              (survivorAssumedLaterWeekly z i))
            (survivorExcludedTransferGrowth z i)
        afSurvivorCombinedMinimum gmpMonthly antifrankWeekly
      else 0
    (gmpProtectedDirectEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum =
      gmpProtectedStateEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum) ∧
    (gmpProtectedDirectEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum =
      gmpProtectedReplacementEPV n h retirement guarantee p disc a b c
        sa sb estate ga gb gc gs ge memberSupplement survivorMinimum +
      gmpProtectedDisplaceableEPV n h retirement guarantee p disc a b
        sa sb gs survivorMinimum) ∧
    (∀ z ∈ Finset.range n,
      a z ≤ awardBase a b z ∧ b z ≤ awardBase a b z) ∧
    (∀ z i j t, t ≤ h →
      survivorMinimum z i j t ≤
        gmpProtectedSurvivorReplacement
          (estateDue h retirement guarantee i t = 1)
          (gmpProtectedContractualSurvivor h z i j t a b sa sb gs)
          (survivorMinimum z i j t)) ∧
    (∀ z i t, t ≤ h →
      memberDue retirement i t = 1 →
      gmpPayableDate ≤ dateOf t →
      afStatutoryWeeklyToMonthly (memberStatutoryWeekly z t) ≤
      fixedChoicePayment a b ga gb z t +
        c z * gc t + memberSupplement z i t) := by
  sorry
