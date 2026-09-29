-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.minimum_positive_moment
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:38:53.097684+00:00
-- url     : https://prove2.me/submissions/bee8dba1-5fd3-4684-8610-cb4e0ef016f4

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finite_channel_moment_certificate
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_attainable_moment_ideal
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_gcd_quotient_pos
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_local_channelLCM_pos
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



















lemma minimumMoment_pos {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p := by
  have hcert := finite_channel_moment_certificate hD hp hDp hpD
  unfold minimumMoment
  apply mul_pos
  · exact_mod_cast local_channelLCM_pos D
  · apply gcd_quotient_pos
    exact_mod_cast hcert.1
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    {m : ℤ} (hm : AttainsMoment D m) (hpos : 0 < m) : minimumMoment D p ≤ m := by
  obtain ⟨k, hk⟩ := (attainable_moment_ideal hD hp hDp hpD m).mp hm
  have hmu := minimumMoment_pos hD hp hDp hpD
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k ≤ 0 := by omega
    have hz := mul_nonpos_of_nonneg_of_nonpos hmu.le hk0
    omega
  calc
    minimumMoment D p = minimumMoment D p * 1 := by ring
    _ ≤ minimumMoment D p * k := mul_le_mul_of_nonneg_left hkpos hmu.le
    _ = m := hk.symm
