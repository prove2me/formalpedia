-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.canonicalKernel_expansion
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:54.453956+00:00
-- url     : https://prove2.me/submissions/40ad214b-c5ad-48a3-bb42-7da3ebff8b85

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_smul
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_add
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_single
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



lemma channelSynthesis_sub (a b : ℕ →₀ ℤ) :
    channelSynthesis (a - b) = channelSynthesis a - channelSynthesis b := by
  have hn : channelSynthesis (-b) = -channelSynthesis b := by
    simpa using channelSynthesis_smul (-1) b
  rw [sub_eq_add_neg, channelSynthesis_add, hn, sub_eq_add_neg]

lemma channelSynthesis_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℤ) :
    channelSynthesis (∑ i ∈ s, a i) = ∑ i ∈ s, channelSynthesis (a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [channelSynthesis]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, channelSynthesis_add, ih]
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (D : ℕ) :
    canonicalKernel D = (channelLCM D : ℤ) • single 1 1 -
      ∑ d ∈ Finset.Icc 2 D,
        ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1)) • isolatedChannelUnit d := by
  classical
  unfold canonicalKernel kernelCoordinates
  rw [channelSynthesis_sub, channelSynthesis_single, channelSynthesis_sum]
  simp only [channelBasisColumn, if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hn : d - 1 ≠ 0 := by omega
  have he : d - 1 + 1 = d := by omega
  rw [channelSynthesis_single]
  simp [channelBasisColumn, hn, he]
