-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.existsUnique_channel_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:34:38.071924+00:00
-- url     : https://prove2.me/submissions/a8b9661a-8cb5-48c3-bb2a-26f826cb4fa4

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_injective
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_exists_synthesis_of_bounded_support
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
theorem solution (f : ℕ →₀ ℤ) (hzero : f 0 = 0) :
    ∃! a : ℕ →₀ ℤ, channelSynthesis a = f := by
  classical
  let N := f.support.sup id
  have hbound : ∀ i : ℕ, N < i → f i = 0 := by
    intro i hi
    by_contra hfi
    have hmem : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    have hle : i ≤ N := Finset.le_sup (f := id) hmem
    omega
  obtain ⟨a, ha⟩ := exists_synthesis_of_bounded_support N f hzero hbound
  exact ⟨a, ha, fun b hb => channelSynthesis_injective (hb.trans ha.symm)⟩
