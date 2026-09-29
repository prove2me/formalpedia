-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.channelSynthesis_injective
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:32:09.750213+00:00
-- url     : https://prove2.me/submissions/5050ba80-4fb7-475f-9924-2b4c7fabddc8

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_moment
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_channel
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
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution : Function.Injective channelSynthesis := by
  intro a b hab
  have hzero := congrArg factorialMoment hab
  rw [synthesis_moment, synthesis_moment] at hzero
  ext j
  by_cases hj : j = 0
  · simpa [hj] using hzero
  · have hd : 2 ≤ j + 1 := by omega
    have hchan : channelNumerator (channelSynthesis a) (j + 1) =
        channelNumerator (channelSynthesis b) (j + 1) :=
      congrArg (fun f => channelNumerator f (j + 1)) hab
    rw [synthesis_channel _ _ hd, synthesis_channel _ _ hd] at hchan
    have hfac : (1 : ℤ) < (j + 1).factorial := by
      exact_mod_cast Nat.one_lt_factorial.mpr hd
    have hne : ((j + 1).factorial : ℤ) - 1 ≠ 0 := by omega
    have hmul : (((j + 1).factorial : ℤ) - 1) * a j =
        (((j + 1).factorial : ℤ) - 1) * b j := by
      rw [hzero] at hchan
      simpa only [Nat.add_sub_cancel] using (add_left_cancel hchan)
    exact mul_left_cancel₀ hne hmul
