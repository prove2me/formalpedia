-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.support_equation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:53.248083+00:00
-- url     : https://prove2.me/submissions/862393ff-8d17-4e3f-803a-05981f428000

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_admissible_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_at_zero
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_at_zero
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

   
                                                                      
                                                                        
                                                                 
                       
  

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D : ℕ} {t : ℤ} {z : ℕ →₀ ℤ} :
    Admissible (t • canonicalKernel D + channelSynthesis z) ↔
      t * kernelOne D + channelSynthesis z 1 = 0 := by
  rw [admissible_iff]
  simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    canonicalKernel_at_zero, synthesis_at_zero, kernelOne]
