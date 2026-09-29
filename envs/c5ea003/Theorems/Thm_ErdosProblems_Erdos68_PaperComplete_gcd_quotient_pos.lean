-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_gcd_quotient_pos
-- name    : ErdosProblems.Erdos68.PaperComplete.gcd_quotient_pos
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:14:23.782715+00:00
-- url     : https://prove2.me/theorems/a26dc7dc-5f58-4ee7-8395-858aec2f2cc0
-- title:
--   Gcd quotient pos
-- statement:
--   For positive integer g, the quotient g/gcd(g,a) is positive.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteIntegerSpan.lean#L120-L128
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

theorem ErdosProblems.Erdos68.PaperComplete.gcd_quotient_pos (g a : ℤ) (hg : 0 < g) :
    0 < g / (Int.gcd g a : ℤ) := by sorry
