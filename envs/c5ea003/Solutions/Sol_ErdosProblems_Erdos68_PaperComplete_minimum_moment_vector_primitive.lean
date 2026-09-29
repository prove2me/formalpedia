-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.minimum_moment_vector_primitive
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:43:11.07651+00:00
-- url     : https://prove2.me/submissions/8c83a2e6-b6f4-4132-b783-2c85b4d40728

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_admissible_iff
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_smul
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finite_channel_moment_certificate
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_smul
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_gcd_quotient_pos
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_local_channelLCM_pos
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_minimum_positive_moment
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
    {f : ℕ →₀ ℤ} (hf : Admissible f) (hc : LowChannels D f)
    (hm : factorialMoment f = minimumMoment D p) : PrimitiveVector f := by
  intro k hk
  rintro ⟨g, he⟩
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℤ) ≠ 0 := by omega
  have hf01 := (admissible_iff f).mp hf
  have hg : Admissible g := by
    apply (admissible_iff g).mpr
    constructor
    · have hz : (k : ℤ) * g 0 = 0 := by
        simpa [he, Finsupp.smul_apply, smul_eq_mul] using hf01.1
      exact (mul_eq_zero.mp hz).resolve_left hk0
    · have hz : (k : ℤ) * g 1 = 0 := by
        simpa [he, Finsupp.smul_apply, smul_eq_mul] using hf01.2
      exact (mul_eq_zero.mp hz).resolve_left hk0
  have hgc : LowChannels D g := by
    intro d hd
    have hz := hc d hd
    rw [he, channelNumerator_smul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hk0
  rw [he, factorialMoment_smul] at hm
  have hmu := minimumMoment_pos hD hp hDp hpD
  have hgm : 0 < factorialMoment g := by
    by_contra h
    have hz := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ k by omega)
      (show factorialMoment g ≤ 0 by omega)
    omega
  have hmin := minimum_positive_moment hD hp hDp hpD
    (show AttainsMoment D (factorialMoment g) from ⟨g, hg, hgc, rfl⟩) hgm
  have hkMul := mul_le_mul_of_nonneg_right hkZ hgm.le
  nlinarith [hm, hkMul]
