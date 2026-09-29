-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.low_channel_classification
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:36:14.355723+00:00
-- url     : https://prove2.me/submissions/bbf1ef7a-5a75-4866-a844-6a4c6768de36

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_kernelCoordinates_zero
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_moment
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_smul
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_kernelCoordinates_pos
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_smul
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_add
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_channel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_channel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_add
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_existsUnique_channel_coordinates
import Theorems.Thm_ErdosProblems_Erdos68_channelLCM_dvd_factorialMoment_of_channels_zero
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







lemma gap_dvd_channelLCM {D d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) :
    ((d.factorial : ℤ) - 1) ∣ (channelLCM D : ℤ) := by
  have hn : d.factorial - 1 ∣ channelLCM D :=
    Finset.dvd_lcm (f := fun n => n.factorial - 1) (Finset.mem_Icc.mpr ⟨hd, hdD⟩)
  have hf : 1 ≤ d.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hz : ((d.factorial - 1 : ℕ) : ℤ) ∣ (channelLCM D : ℤ) := by
    exact_mod_cast hn
  simpa [Nat.cast_sub hf] using hz































lemma tail_channels {D : ℕ} (hD : 1 ≤ D) {z : ℕ →₀ ℤ}
    (hz : TailCoordinates D z) : LowChannels D (channelSynthesis z) := by
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hdD := (Finset.mem_Icc.mp hd).2
  rw [synthesis_channel _ _ hd2, hz 0 (by omega), hz (d - 1) (by omega)]
  ring
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D : ℕ} (hD : 2 ≤ D)
    (f : ℕ →₀ ℤ) (h0 : f 0 = 0) :
    LowChannels D f ↔ ∃ t : ℤ, ∃ z : ℕ →₀ ℤ,
      TailCoordinates D z ∧ f = t • canonicalKernel D + channelSynthesis z := by
  classical
  constructor
  · intro hf
    obtain ⟨a, ha, _⟩ := existsUnique_channel_coordinates f h0
    obtain ⟨t, ht⟩ := channelLCM_dvd_factorialMoment_of_channels_zero D f hf
    let z := a - t • kernelCoordinates D
    have ha0 : a 0 = factorialMoment f := by rw [← ha, synthesis_moment]
    have hz : TailCoordinates D z := by
      intro j hj
      change a j - (t • kernelCoordinates D) j = 0
      rw [Finsupp.smul_apply, smul_eq_mul]
      by_cases hj0 : j = 0
      · subst j
        rw [kernelCoordinates_zero, ha0, ht]
        ring
      · have hjp : 0 < j := by omega
        have hd2 : 2 ≤ j + 1 := by omega
        have hdD : j + 1 ≤ D := by omega
        have hc := hf (j + 1) (Finset.mem_Icc.mpr ⟨hd2, hdD⟩)
        rw [← ha, synthesis_channel _ _ hd2] at hc
        simp only [Nat.add_sub_cancel] at hc
        have hq := Int.mul_ediv_cancel' (gap_dvd_channelLCM hd2 hdD)
        have hfac : (1 : ℤ) < (j + 1).factorial := by
          exact_mod_cast Nat.one_lt_factorial.mpr hd2
        have hne : ((j + 1).factorial : ℤ) - 1 ≠ 0 := by omega
        rw [kernelCoordinates_pos hjp D, if_pos hdD]
        apply mul_left_cancel₀ hne
        rw [mul_zero]
        rw [ha0, ht] at hc
        nlinarith [hc, congrArg (fun x : ℤ => t * x) hq]
    refine ⟨t, z, hz, ?_⟩
    dsimp [z]
    rw [channelSynthesis_sub, channelSynthesis_smul, ha]
    change f = t • canonicalKernel D + (f - t • canonicalKernel D)
    abel
  · rintro ⟨t, z, hz, rfl⟩ d hd
    rw [channelNumerator_add, channelNumerator_smul,
      canonicalKernel_channel (Finset.mem_Icc.mp hd).1,
      if_pos (Finset.mem_Icc.mp hd).2,
      tail_channels (by omega) hz d hd]
    ring
