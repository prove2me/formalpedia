-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.synthesis_channel
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:29:35.511988+00:00
-- url     : https://prove2.me/submissions/9c285f86-1653-48c1-b41d-d2696f9161b1

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_single
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_smul
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_sum
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_isolatedChannelUnit
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Full integral coordinate theorem

Short label res:divisor-channel-coordinates. The supplied library proves the
isolated moment/channel values, but does not prove spanning and uniqueness.
Here the auxiliary index 1 is represented by coordinate 0, and coordinate j>0
represents U_(j+1). Thus coordinates have type ℕ →₀ ℤ with no constrained
coordinate. The target coefficient vectors satisfy f 0 = 0, exactly the
paper's index convention n≥1 before its later restriction to n≥2.

The proof supplies spanning by triangular elimination, independence by the
moment/channel observables, and the explicit coefficient formula. This is
stronger than checking finitely many example matrices.
STATUS: compiled proof candidate. No axioms or proof placeholders.
-/

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp















lemma basisColumn_channel (j d : ℕ) (hd : 2 ≤ d) :
    channelNumerator (channelBasisColumn j) d =
      (if j = 0 then 1 else 0) +
      (if j = d - 1 then (d.factorial : ℤ) - 1 else 0) := by
  by_cases hj : j = 0
  · subst j
    have hdn : ¬ (0 : ℕ) = d - 1 := by omega
    have h1d : (1 : ℕ) < d := by omega
    simp [channelBasisColumn, channelNumerator_single, channelWeight,
      Nat.div_eq_of_lt h1d, hdn]
  · have hj2 : 2 ≤ j + 1 := by omega
    rw [channelBasisColumn, if_neg hj,
      channelNumerator_isolatedChannelUnit hj2 hd]
    by_cases heq : d = j + 1
    · subst d
      simp [hj]
    · have hne : j ≠ d - 1 := by omega
      simp [heq, hj, hne]
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (a : ℕ →₀ ℤ) (d : ℕ) (hd : 2 ≤ d) :
    channelNumerator (channelSynthesis a) d =
      a 0 + ((d.factorial : ℤ) - 1) * a (d - 1) := by
  classical
  change channelNumerator (∑ j ∈ a.support, a j • channelBasisColumn j) d = _
  rw [channelNumerator_sum]
  simp_rw [channelNumerator_smul, basisColumn_channel _ d hd, mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ j ∈ a.support, a j * (if j = 0 then (1 : ℤ) else 0)) = a 0 := by
    by_cases ha : a 0 = 0 <;> simp [mul_ite, ha, Finsupp.mem_support_iff]
  have hsecond : (∑ j ∈ a.support, a j *
      (if j = d - 1 then (d.factorial : ℤ) - 1 else 0)) =
      ((d.factorial : ℤ) - 1) * a (d - 1) := by
    by_cases ha : a (d - 1) = 0 <;>
      simp [mul_ite, ha, Finsupp.mem_support_iff, mul_comm]
  rw [hfirst, hsecond]
