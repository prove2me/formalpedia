-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.coprime_sumSquares_square_dvd48
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:27:42.001245+00:00
-- url     : https://prove2.me/submissions/6f914a5c-b11f-4b53-a6ab-50e42e81d729

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime r s) (hd : (r ^ 2 + s ^ 2) ^ 2 ∣ 48) :
    r = 1 ∧ s = 1 := by
  have hbound : (r ^ 2 + s ^ 2) ^ 2 ≤ 48 := Nat.le_of_dvd (by decide) hd
  have hnorm : r ^ 2 + s ^ 2 ≤ 6 := by
    by_contra hnot
    have hge : 7 ≤ r ^ 2 + s ^ 2 := by omega
    have hh := Nat.mul_le_mul hge hge
    nlinarith
  have hr1 : 1 ≤ r := hr
  have hs1 : 1 ≤ s := hs
  have hr2 : r ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ r := by omega
    have hh := Nat.mul_le_mul hge hge
    have hh' := Nat.mul_le_mul hs1 hs1
    nlinarith
  have hs2 : s ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ s := by omega
    have hh := Nat.mul_le_mul hge hge
    have hh' := Nat.mul_le_mul hr1 hr1
    nlinarith
  interval_cases r <;> interval_cases s <;> norm_num at *
