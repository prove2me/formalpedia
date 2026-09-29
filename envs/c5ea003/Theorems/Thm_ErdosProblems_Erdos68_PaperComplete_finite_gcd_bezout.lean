-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finite_gcd_bezout
-- name    : ErdosProblems.Erdos68.PaperComplete.finite_gcd_bezout
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:06:02.00386+00:00
-- url     : https://prove2.me/theorems/fd93e27f-abea-4914-a19b-74de322ef2f4
-- title:
--   Finite gcd bezout
-- statement:
--   The gcd of finitely many integer weights is an integer linear combination with coefficients supported on that finite set.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L47-L79
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

theorem ErdosProblems.Erdos68.PaperComplete.finite_gcd_bezout (s : Finset ℕ) (w : ℕ → ℤ) :
    ∃ z : ℕ →₀ ℤ, SupportedOn z s ∧
      integerEvaluation w z = ((s.gcd (fun i => (w i).natAbs) : ℕ) : ℤ) := by sorry
