-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_denominator_dvd48
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:30.88111+00:00
-- url     : https://prove2.me/submissions/954e5811-7f24-4ae7-ac9a-960bdec240d6

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- The denominator in the rational parameterisation is coprime to both
parameter coordinates, not merely to a selected finite set of primes. -/
theorem coprime_sumSquares_coordinates (r s : ℕ) (hcop : Nat.Coprime r s) :
    Nat.Coprime (r ^ 2 + s ^ 2) r ∧ Nat.Coprime (r ^ 2 + s ^ 2) s := by
  have hrr : r ∣ r ^ 2 := ⟨r, by ring⟩
  have hss : s ∣ s ^ 2 := ⟨s, by ring⟩
  constructor
  · rw [Nat.add_coprime_iff_right hrr]
    exact hcop.symm.pow_left 2
  · rw [Nat.add_coprime_iff_left hss]
    exact hcop.pow_left 2
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (m r s : ℕ) (hcop : Nat.Coprime r s)
    (heq : m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r ^ 3 * s ∨
      m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r * s ^ 3) :
    (r ^ 2 + s ^ 2) ^ 2 ∣ 48 := by
  obtain ⟨hr, hs⟩ := coprime_sumSquares_coordinates r s hcop
  rcases heq with heq | heq
  · have hc : Nat.Coprime ((r ^ 2 + s ^ 2) ^ 2) (r ^ 3 * s) :=
      Nat.coprime_mul_iff_right.mpr ⟨(hr.pow_left 2).pow_right 3, hs.pow_left 2⟩
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  · have hc : Nat.Coprime ((r ^ 2 + s ^ 2) ^ 2) (r * s ^ 3) :=
      Nat.coprime_mul_iff_right.mpr ⟨hr.pow_left 2, (hs.pow_left 2).pow_right 3⟩
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
