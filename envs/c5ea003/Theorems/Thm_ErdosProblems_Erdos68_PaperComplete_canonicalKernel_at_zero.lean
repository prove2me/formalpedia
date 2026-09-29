-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_at_zero
-- name    : ErdosProblems.Erdos68.PaperComplete.canonicalKernel_at_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:03:35.945493+00:00
-- url     : https://prove2.me/theorems/bd65dc74-5eb0-44eb-87de-e269b52ea64e
-- title:
--   Canonical Kernel at zero
-- statement:
--   The canonical depth-D kernel has zero coefficient at index zero.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteLowKernel.lean#L146-L147
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

   
                                                                      
                                                                        
                                                                 
                       
  
open scoped BigOperators
open Finsupp

open ErdosProblems.Erdos68.PaperComplete

theorem ErdosProblems.Erdos68.PaperComplete.canonicalKernel_at_zero (D : ℕ) : canonicalKernel D 0 = 0 := by sorry
