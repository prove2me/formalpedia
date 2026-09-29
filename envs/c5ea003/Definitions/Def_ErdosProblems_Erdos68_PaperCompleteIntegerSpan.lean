-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
-- name    : ErdosProblems_Erdos68_PaperCompleteIntegerSpan
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T15:49:07.401018+00:00
-- url     : https://prove2.me/theorems/2ef276a9-fc93-4baa-97d7-234e5bed14f7
-- title:
--   Supported integer evaluations
-- statement:
--   Defines support restriction for a finite coordinate vector and its integer-weight evaluation. Finite Bézout attainment and divisibility are separate theorem nodes.
-- source:
--   Pinned Lean definition SupportedOn: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L12-L13
--   Pinned Lean definition integerEvaluation: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L15-L16
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

   
                                                                  
                                                                              
  
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

def SupportedOn (z : ℕ →₀ ℤ) (s : Finset ℕ) : Prop :=
  ∀ i, i ∉ s → z i = 0

noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)

















end ErdosProblems.Erdos68.PaperComplete


