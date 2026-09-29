-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.canonicalKernel_channel
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:32:09.109677+00:00
-- url     : https://prove2.me/submissions/08ff04fc-781e-4e17-9f90-488cf7f54ae9

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_kernelCoordinates_zero
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_kernelCoordinates_pos
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_channel
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











lemma gap_dvd_channelLCM {D d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) :
    ((d.factorial : ℤ) - 1) ∣ (channelLCM D : ℤ) := by
  have hn : d.factorial - 1 ∣ channelLCM D :=
    Finset.dvd_lcm (f := fun n => n.factorial - 1) (Finset.mem_Icc.mpr ⟨hd, hdD⟩)
  have hf : 1 ≤ d.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hz : ((d.factorial - 1 : ℕ) : ℤ) ∣ (channelLCM D : ℤ) := by
    exact_mod_cast hn
  simpa [Nat.cast_sub hf] using hz
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D d : ℕ} (hd : 2 ≤ d) :
    channelNumerator (canonicalKernel D) d =
      if d ≤ D then 0 else (channelLCM D : ℤ) := by
  have hj : 0 < d - 1 := by omega
  have he : d - 1 + 1 = d := by omega
  rw [canonicalKernel, synthesis_channel _ _ hd, kernelCoordinates_zero,
    kernelCoordinates_pos hj, he]
  by_cases h : d ≤ D
  · rw [if_pos h, if_pos h]
    have hq := Int.mul_ediv_cancel' (gap_dvd_channelLCM hd h)
    nlinarith [hq]
  · simp [h]
