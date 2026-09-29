-- Prove2me | solution 1 for ErdosProblems.Erdos257.card_Icc_one_filter_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:09:22.639827+00:00
-- url     : https://prove2.me/submissions/ded3b139-46bf-41a2-9fa3-cba75fa7c758

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Mathlib

/-!
# Cover-independent periodic means

Lemma A.1 of the 2026-09-06 Type B revision return: a nonnegative divisor
majorant of `g` controls every Cesàro average of `g`, hence every periodic
mean. This is not an irrationality theorem. It bounds cover cost.

The coprime-cover obstruction (Type B Theorem B.1) uses this averaging plus
the elementary density `1 - ∏(1 - 1/a)`; that density identity is recorded
as an ordinary proof in `VariableExponentCoverSeparation.md`.
-/

namespace ErdosProblems.Erdos257
open Finset
end ErdosProblems.Erdos257

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution {d X : ℕ} (hd : 0 < d) :
    ((Icc 1 X).filter (fun n => d ∣ n)).card = X / d := by
  have hsrc : (Icc 1 (X / d)).card = X / d := by
    simpa using Nat.card_Icc 1 (X / d)
  refine hsrc ▸ (card_bij (fun k _ => k * d) ?_ ?_ ?_).symm
  · intro k hk
    have hkIcc := mem_Icc.mp hk
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_left d k⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_le_iff.mp hkIcc.1) hd)
    · exact (Nat.le_div_iff_mul_le hd).mp hkIcc.2
  · intro a ha b hb h
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa [mul_comm] using h)
  · intro n hn
    have hn' := mem_filter.mp hn
    have hnIcc := mem_Icc.mp hn'.1
    obtain ⟨k, hk⟩ := hn'.2
    have hkpos : 0 < k := by
      have hnpos : 0 < n := Nat.succ_le_iff.mp hnIcc.1
      rw [hk] at hnpos
      exact Nat.pos_of_mul_pos_left hnpos
    refine ⟨k, mem_Icc.mpr ⟨Nat.succ_le_of_lt hkpos, ?_⟩, by rw [hk, mul_comm]⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by
      rw [mul_comm, ← hk]
      exact hnIcc.2)
