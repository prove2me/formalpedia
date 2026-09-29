-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_gcd_quotient_dvd_iff
-- name    : ErdosProblems.Erdos68.PaperComplete.gcd_quotient_dvd_iff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:06:24.389057+00:00
-- url     : https://prove2.me/theorems/d820c2a5-5f6c-4eba-88a3-dce5a400af64
-- title:
--   Gcd quotient divisibility equivalence
-- statement:
--   For positive g, g/gcd(g,a) divides t exactly when g divides t times a.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L82-L118
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

theorem ErdosProblems.Erdos68.PaperComplete.gcd_quotient_dvd_iff (g a t : ℤ) (hg : 0 < g) :
    g / (Int.gcd g a : ℤ) ∣ t ↔ g ∣ t * a := by sorry
