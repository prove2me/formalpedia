-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_nat_classification
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:51:04.551887+00:00
-- url     : https://prove2.me/submissions/45c975ed-742e-4423-b263-1878b27251e5

import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_coprime_sumSquares_square_dvd48
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_denominator_dvd48
import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (m r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hcop : Nat.Coprime r s)
    (heq : m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r ^ 3 * s ∨
      m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r * s ^ 3) :
    r = 1 ∧ s = 1 ∧ m = 12 := by
  have hd := cubic_scale_denominator_dvd48 m r s hcop heq
  obtain ⟨hr1, hs1⟩ := coprime_sumSquares_square_dvd48 r s hr hs hcop hd
  refine ⟨hr1, hs1, ?_⟩
  rw [hr1, hs1] at heq
  rcases heq with heq | heq <;> norm_num at heq <;> omega
