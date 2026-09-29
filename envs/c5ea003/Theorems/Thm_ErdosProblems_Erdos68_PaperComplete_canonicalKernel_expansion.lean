-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_expansion
-- name    : ErdosProblems.Erdos68.PaperComplete.canonicalKernel_expansion
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:14:10.494781+00:00
-- url     : https://prove2.me/theorems/5e2fe9fe-9883-4b18-be42-31b325b691d4
-- title:
--   Canonical Kernel expansion
-- statement:
--   The canonical kernel equals channelLCM D times the single coefficient at one minus the stated finite sum of isolated units at channels 2 through D.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteLowKernel.lean#L112-L127
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

theorem ErdosProblems.Erdos68.PaperComplete.canonicalKernel_expansion (D : ℕ) :
    canonicalKernel D = (channelLCM D : ℤ) • single 1 1 -
      ∑ d ∈ Finset.Icc 2 D,
        ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1)) • isolatedChannelUnit d := by sorry
