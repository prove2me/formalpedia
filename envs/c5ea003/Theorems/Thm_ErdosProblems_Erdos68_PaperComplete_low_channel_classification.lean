-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_low_channel_classification
-- name    : ErdosProblems.Erdos68.PaperComplete.low_channel_classification
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:14:12.827977+00:00
-- url     : https://prove2.me/theorems/a80a5c97-5da5-4800-8546-addeb8844ba0
-- title:
--   Low channel classification
-- statement:
--   For D≥2 and f(0)=0, vanishing channels 2 through D is equivalent to a decomposition f=t times the canonical kernel plus synthesis of coordinates zero below D.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteLowKernel.lean#L190-L234
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

theorem ErdosProblems.Erdos68.PaperComplete.low_channel_classification {D : ℕ} (hD : 2 ≤ D)
    (f : ℕ →₀ ℤ) (h0 : f 0 = 0) :
    LowChannels D f ↔ ∃ t : ℤ, ∃ z : ℕ →₀ ℤ,
      TailCoordinates D z ∧ f = t • canonicalKernel D + channelSynthesis z := by sorry
