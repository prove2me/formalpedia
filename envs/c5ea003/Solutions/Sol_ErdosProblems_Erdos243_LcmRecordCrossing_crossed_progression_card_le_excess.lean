-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_card_le_excess
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:53:19.647545+00:00
-- url     : https://prove2.me/submissions/f238d159-2e10-4db6-874e-45a48848d652

import Mathlib
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_crossed_progression_spacing
open ErdosProblems.Erdos243 ErdosProblems.Erdos243.LcmRecordCrossing

private theorem covered_wall_forces_excess {U d L a tau B : ℤ}
    (hd : 0 < d) (hsource : U < tau) (hcross : tau ≤ U + d)
    (hfeedback : d = (a - 1) * U - L)
    (hcover : ∀ z : ℤ, tau - B ≤ z → z < tau →
      ∃ m : ℤ, B < m ∧ m ∣ L ∧ m ∣ z) : B < d := by
  by_contra h
  have hsmall : d ≤ B := by omega
  obtain ⟨m, hm, hmL, hmU⟩ := hcover U (by omega) hsource
  have hmd : m ∣ d := by
    rw [hfeedback]
    exact dvd_sub (dvd_mul_of_dvd_right hmU (a - 1)) hmL
  have hle : m ≤ d := Int.le_of_dvd hd hmd
  omega

private theorem wall_count_le_excess {h P d B : ℕ}
    (hP : B < P) (hd : B < d)
    (hspacing : (h - 1) * P < d) : h ≤ d - B := by
  by_contra hh
  have hge : d - B ≤ h - 1 := by omega
  have hmul : (d - B) * P ≤ (h - 1) * P := Nat.mul_le_mul_right P hge
  have hrem : 1 ≤ d - B := by omega
  have hBP : B + 1 ≤ P := by omega
  have hbound : d ≤ (d - B) * P := by
    have hmul2 := Nat.mul_le_mul_left (d - B) hBP
    have hmul3 := Nat.mul_le_mul_right B hrem
    have hsplit : d - B + B = d := Nat.sub_add_cancel (by omega)
    nlinarith
  omega

theorem solution (s : Finset ℕ)
    (x P U d B : ℕ) (a L : ℤ) (hP : B < P)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d)
    (hfeedback : (d : ℤ) = (a - 1) * U - L)
    (hcover : ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L ∧ m ∣ z) :
    s.card ≤ d - B := by
  by_cases hs : s.Nonempty
  · obtain ⟨k, hk⟩ := hs
    have hd : 0 < d := by have := hlo k hk; have := hhi k hk; omega
    have hexcess : (B : ℤ) < d :=
      covered_wall_forces_excess (U := U) (d := d) (L := L) (a := a)
        (tau := (x + k * P : ℕ)) (B := B)
        (by exact_mod_cast hd) (by exact_mod_cast hlo k hk)
        (by exact_mod_cast hhi k hk) hfeedback (hcover k hk)
    apply wall_count_le_excess hP (by exact_mod_cast hexcess)
    exact crossed_progression_spacing s ⟨k, hk⟩ x P U d hlo hhi
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]
