-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.tail_one_eq_integerEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:41.345828+00:00
-- url     : https://prove2.me/submissions/daeea2bd-5ed1-48bd-97cd-a74fdd563b16

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
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
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D : ℕ} (hD : 1 ≤ D)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    channelSynthesis z 1 = integerEvaluation (fun j => channelScalar (j + 1)) z := by
  classical
  unfold channelSynthesis integerEvaluation Finsupp.sum
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD : D ≤ j := by
    by_contra h
    have hjz := hz j (by omega)
    exact (Finsupp.mem_support_iff.mp hj) hjz
  have hj0 : j ≠ 0 := by omega
  simp [channelBasisColumn, hj0, channelScalar, Finsupp.smul_apply, smul_eq_mul]
