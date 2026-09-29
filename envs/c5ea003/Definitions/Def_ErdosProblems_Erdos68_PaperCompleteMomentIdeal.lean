-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
-- name    : ErdosProblems_Erdos68_PaperCompleteMomentIdeal
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T16:01:12.814712+00:00
-- url     : https://prove2.me/theorems/888170f8-12af-4cef-8735-0ab87baa55da
-- title:
--   Attainable moments and primitive-vector definitions
-- statement:
--   Defines attainable factorial moments under admissibility and low-channel cancellation, the proposed minimum generator, vector primitivity, and coefficient content. Exact ideal and minimum theorems are separate nodes.
-- source:
--   Pinned Lean definition AttainsMoment: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L95-L96
--   Pinned Lean definition minimumMoment: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L134-L136
--   Pinned Lean definition PrimitiveVector: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L202-L203
--   Pinned Lean definition coefficientContent: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L254-L255
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Combinatorics.Enumerative.Bell
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

   
                                                                            
                                                                              
                                                                              
  
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp











/-- Existence on the literal coefficient domain n>=2. -/
def AttainsMoment (D : ℕ) (m : ℤ) : Prop :=
  ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧ factorialMoment f = m



noncomputable def minimumMoment (D p : ℕ) : ℤ :=
  let G : ℤ := finiteScalarGcd D (D * (2 * p - 1))
  (channelLCM D : ℤ) * (G / (Int.gcd G (kernelOne D) : ℤ))









/-- For a nonzero finite integer vector this is equivalent to coefficient content 1. -/
def PrimitiveVector (f : ℕ →₀ ℤ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℕ →₀ ℤ, f = (k : ℤ) • g





/-- Literal coefficient content, including the empty-vector convention gcd(empty)=0. -/
noncomputable def coefficientContent (f : ℕ →₀ ℤ) : ℕ :=
  f.support.gcd (fun n => (f n).natAbs)











end ErdosProblems.Erdos68.PaperComplete


