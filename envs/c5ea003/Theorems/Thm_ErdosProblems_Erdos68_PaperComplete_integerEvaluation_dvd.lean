-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_integerEvaluation_dvd
-- name    : ErdosProblems.Erdos68.PaperComplete.integerEvaluation_dvd
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:06:32.276287+00:00
-- url     : https://prove2.me/theorems/3ed69498-7250-4f72-bb24-5fd30c15ed97
-- title:
--   Integer Evaluation divisibility
-- statement:
--   If g divides every weight on the support of a finite coefficient vector, it divides that vector's integer evaluation.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L40-L44
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
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

   
                                                                  
                                                                              
  
open scoped BigOperators
open Finsupp

open ErdosProblems.Erdos68.PaperComplete

theorem ErdosProblems.Erdos68.PaperComplete.integerEvaluation_dvd (w : ℕ → ℤ) (z : ℕ →₀ ℤ) (g : ℤ)
    (h : ∀ i ∈ z.support, g ∣ w i) : g ∣ integerEvaluation w z := by sorry
