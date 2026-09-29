-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.synthesis_moment
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:36.82753+00:00
-- url     : https://prove2.me/submissions/a0cedb48-f9c6-4a94-8a5a-9ffc1713112a

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_smul
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_sum
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_basisColumn_moment
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
theorem solution (a : ℕ →₀ ℤ) :
    factorialMoment (channelSynthesis a) = a 0 := by
  classical
  change factorialMoment (∑ j ∈ a.support, a j • channelBasisColumn j) = _
  rw [factorialMoment_sum]
  simp_rw [factorialMoment_smul, basisColumn_moment]
  by_cases ha : a 0 = 0
  · simp [mul_ite, ha, Finsupp.mem_support_iff]
  · simp [mul_ite, ha, Finsupp.mem_support_iff]
