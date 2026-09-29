-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.low_coordinate_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:04:14.866369+00:00
-- url     : https://prove2.me/submissions/4b0c8eee-0607-4796-b08f-30a2d38fbb42

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

   
                                                                      
                                                                        
                                                                 
                       
  

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (D j : ℕ) :
    (∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))) j =
      if 1 ≤ j ∧ j + 1 ≤ D then
        (channelLCM D : ℤ) / (((j + 1).factorial : ℤ) - 1) else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  by_cases h : 1 ≤ j ∧ j + 1 ≤ D
  · rw [if_pos h, Finset.sum_eq_single (j + 1)]
    · simp
    · intro d hd hne
      have hd2 := (Finset.mem_Icc.mp hd).1
      have hneq : d - 1 ≠ j := by omega
      simp [Finsupp.single_apply, hneq]
    · intro hn
      exact (hn (Finset.mem_Icc.mpr ⟨by omega, h.2⟩)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    have hdD := (Finset.mem_Icc.mp hd).2
    have hneq : d - 1 ≠ j := by omega
    simp [Finsupp.single_apply, hneq]
