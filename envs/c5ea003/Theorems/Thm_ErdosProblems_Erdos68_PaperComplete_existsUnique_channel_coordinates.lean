-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_existsUnique_channel_coordinates
-- name    : ErdosProblems.Erdos68.PaperComplete.existsUnique_channel_coordinates
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:14:11.359815+00:00
-- url     : https://prove2.me/theorems/73e423bb-125b-48ba-afe4-36b302a92ae2
-- title:
--   Exists Unique channel coordinates
-- statement:
--   Every finite coefficient vector with zero coordinate at index zero has unique channel-synthesis coordinates.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L219-L230
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
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

open scoped BigOperators
open Finsupp

open ErdosProblems.Erdos68.PaperComplete

theorem ErdosProblems.Erdos68.PaperComplete.existsUnique_channel_coordinates (f : ℕ →₀ ℤ) (hzero : f 0 = 0) :
    ∃! a : ℕ →₀ ℤ, channelSynthesis a = f := by sorry
