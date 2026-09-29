-- Prove2me | solution 1 for mme_HasPrescribedZSix_of_constant_grade_oneHot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:01:36.085016+00:00
-- url     : https://prove2.me/submissions/4b5879f4-f491-4ddc-8852-acf035814b7f

import Mathlib.Tactic
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot

set_option autoImplicit false
set_option warningAsError true

universe u

open MME BigOperators Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue

/-- Ordinary six-value transfers without a rate loss when the prescribed
Z histogram is already forced by a constant basis grade. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a,
      p.count a = if a = a0 then p.denominator else 0)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hSix : HasSixSymmetricTauValueAtLeast T tau V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V := by
  rw [HasPrescribedZSixRestrictionValueAtLeast, HasSixSequenceRate]
  refine ⟨hV, ?_⟩
  intro v hv hvl cutoff
  have hVpos : 0 < V := hv.trans hvl
  have hv0 : 0 ≤ v := hv.le
  have hbase : 0 < V ^ (6 : ℕ) := pow_pos hVpos _
  have htarget : 0 ≤ v ^ (6 : ℕ) := pow_nonneg hv0 _
  have hstrict : v ^ (6 : ℕ) < V ^ (6 : ℕ) :=
    pow_lt_pow_left₀ hvl hv0 (by norm_num)
  have hTau : HasTauValueAtLeast
      (sixSymmetrization T) tau (V ^ (6 : ℕ)) := hSix
  obtain ⟨E, hE, hcommon⟩ :=
    mme_HasTauValueAtLeast_multiple_extractions_below
      (sixSymmetrization T) tau (V ^ (6 : ℕ)) (v ^ (6 : ℕ))
      hbase htarget hstrict hTau
  let r : ℕ := cutoff + 1
  let m : ℕ := r * E
  obtain ⟨q, A, B, C, hrestrict, hweight⟩ := hcommon (p.denominator * r)
  have hEone : 1 ≤ E := hE
  have hrm : r ≤ m := by
    change r ≤ r * E
    calc
      r = r * 1 := by simp
      _ ≤ r * E := Nat.mul_le_mul_left r hEone
  have hcutm : cutoff ≤ m := (Nat.le_succ cutoff).trans hrm
  have hDone : 1 ≤ p.denominator := p.denominator_pos
  have hmLength : m ≤ p.length m := by
    rw [IntegerZSplitProfile.length]
    calc
      m = 1 * m := by simp
      _ ≤ p.denominator * m := Nat.mul_le_mul_right m hDone
  refine ⟨m, hcutm, hcutm.trans hmLength, ?_⟩
  refine ⟨q, A, B, C, ?_, ?_⟩
  have hrestrictPower : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
      ((sixSymmetrization T).kronPow (p.denominator * m)) := by
    simpa [m, Nat.mul_assoc] using hrestrict
  have hsymPower : TensorObj.Restrict
      ((sixSymmetrization T).kronPow (p.denominator * m))
      (sixSymmetrization (T.kronPow (p.denominator * m))) :=
    (mme_sixSymmetrization_kronPow_isomorphic T (p.denominator * m)).1
  have hambient : TensorObj.Restrict
      (T.kronPow (p.denominator * m))
      (prescribedZPower T bZ grade p m) := by
    simpa [IntegerZSplitProfile.length] using
      mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot
        T bZ grade p a0 hgrade hone m
  have hsymAmbient : TensorObj.Restrict
      (sixSymmetrization (T.kronPow (p.denominator * m)))
      (sixSymmetrization (prescribedZPower T bZ grade p m)) :=
    mme_sixSymmetrization_restrict hambient
  exact TensorObj.Restrict.trans hrestrictPower
    (TensorObj.Restrict.trans hsymPower hsymAmbient)
  simpa [IntegerZSplitProfile.length, m, pow_mul, Nat.mul_assoc] using hweight
