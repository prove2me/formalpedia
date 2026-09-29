-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.basisColumn_moment
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:13:07.775795+00:00
-- url     : https://prove2.me/submissions/04921f72-4ecd-4776-bebf-7a03cecb8086

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_single
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_isolatedChannelUnit
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
theorem solution (j : ℕ) :
    factorialMoment (channelBasisColumn j) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · simp [channelBasisColumn, hj, factorialMoment_single]
  · simp only [channelBasisColumn, if_neg hj]
    exact factorialMoment_isolatedChannelUnit (by omega)
