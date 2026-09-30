-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.not_summable_recordExcessWeight_of_progression
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:55:54.658421+00:00
-- url     : https://prove2.me/submissions/27f02aad-072d-4375-b9cd-e5cda2b771d8

import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_finite_record_weighted_bound
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordDivergence
open ErdosProblems.Erdos243.LcmRecordCrossing

theorem solution
    (U : ℕ → ℕ) (a L : ℕ → ℤ) (x P B : ℕ) (hP : B < P)
    (hzero : U 0 < x)
    (hunbounded : ∀ t : ℕ, ∃ n, t ≤ U n)
    (hfeedback : ∀ n, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n k : ℕ, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiverges : ¬ Summable (fun k : ℕ => f (x + k * P))) :
    ¬ Summable (recordExcessWeight U B f) := by
  classical
  intro hsum
  apply hdiverges
  have hcharge : ∀ n, 0 ≤ recordExcessWeight U B f n := by
    intro n
    unfold recordExcessWeight
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hpos _)
    · exact le_refl 0
  apply summable_of_sum_le (fun k => hpos (x + k * P))
  intro s
  obtain ⟨N, hN⟩ := hunbounded (s.sup (fun k => x + k * P))
  have hfinite := finite_record_weighted_bound s U a L x P B N hP
    (fun k _hk => lt_of_lt_of_le hzero (Nat.le_add_right x (k * P)))
    (fun k hk => ⟨N, le_refl N, (Finset.le_sup hk).trans hN⟩)
    (fun n _hn => hfeedback n)
    (fun n _hn k _hk => hcover n k) f hf hpos
  calc
    ∑ k ∈ s, f (x + k * P) ≤
        ∑ n ∈ Finset.range N, recordExcessWeight U B f n := by
      simpa only [recordExcessWeight] using hfinite
    _ ≤ ∑' n, recordExcessWeight U B f n :=
      hsum.sum_le_tsum (Finset.range N) (fun n _hn => hcharge n)


