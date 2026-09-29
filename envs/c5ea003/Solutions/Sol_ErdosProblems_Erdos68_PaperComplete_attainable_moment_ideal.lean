-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.attainable_moment_ideal
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:37:40.890431+00:00
-- url     : https://prove2.me/submissions/116dde51-ab92-4a72-b87b-31cf7fcdbf51

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_admissible_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_synthesis_at_zero
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_at_zero
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_smul
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_add
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_moment
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_smul
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finiteScalarGcd_dvd_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finite_channel_moment_certificate
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_finite_gcd_bezout
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_gcd_quotient_dvd_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_integerEvaluation_dvd
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_low_channel_classification
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_support_equation
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_tail_moment
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_tail_one_eq_integerEvaluation
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



lemma shifted_scalar_gcd_eq {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H) :
    (Finset.Icc D (H - 1)).gcd (fun j => (channelScalar (j + 1)).natAbs) =
      finiteScalarGcd D H := by
  apply Nat.dvd_antisymm
  · apply (finiteScalarGcd_dvd_iff D H _).mpr
    intro n hn hnH
    have hm : n - 1 ∈ Finset.Icc D (H - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hdiv := Finset.gcd_dvd
      (f := fun j => (channelScalar (j + 1)).natAbs) hm
    have he : n - 1 + 1 = n := by omega
    dsimp only at hdiv
    rw [he] at hdiv
    exact Int.natCast_dvd.mpr hdiv
  · apply Finset.dvd_gcd
    intro j hj
    have hjD := (Finset.mem_Icc.mp hj).1
    have hjH := (Finset.mem_Icc.mp hj).2
    apply Int.natCast_dvd.mp
    exact (finiteScalarGcd_dvd_iff D H _).mp (dvd_refl _) (j + 1)
      (by omega) (by omega)

/-- An explicit finite support exists for a Bezout generator of the actual gcd. -/
theorem finite_tail_gcd_attained {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H) :
    ∃ z : ℕ →₀ ℤ, TailCoordinates D z ∧
      channelSynthesis z 1 = (finiteScalarGcd D H : ℤ) ∧
      SupportedOn z (Finset.Icc D (H - 1)) := by
  obtain ⟨z, hs, he⟩ := finite_gcd_bezout (Finset.Icc D (H - 1))
    (fun j => channelScalar (j + 1))
  have hz : TailCoordinates D z := by
    intro j hj
    apply hs j
    intro hmem
    have := (Finset.mem_Icc.mp hmem).1
    omega
  refine ⟨z, hz, ?_, hs⟩
  rw [tail_one_eq_integerEvaluation hD hz, he, shifted_scalar_gcd_eq hD hDH]

lemma tail_gcd_dvd_one {D G : ℕ} (hD : 1 ≤ D)
    (hG : IsScalarTailGcd D G) {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    (G : ℤ) ∣ channelSynthesis z 1 := by
  rw [tail_one_eq_integerEvaluation hD hz]
  apply integerEvaluation_dvd
  intro j hj
  have hjD : D ≤ j := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hz j (by omega))
  exact (hG G).mp (dvd_refl G) (j + 1) (by omega)

/-- Integer combinations in the entire tail form precisely G Z. -/
theorem exists_tail_one_iff {D H : ℕ} (hD : 1 ≤ D) (hDH : D < H)
    (hG : IsScalarTailGcd D (finiteScalarGcd D H)) (q : ℤ) :
    (∃ z : ℕ →₀ ℤ, TailCoordinates D z ∧ channelSynthesis z 1 = q) ↔
      (finiteScalarGcd D H : ℤ) ∣ q := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact tail_gcd_dvd_one hD hG hz
  · rintro ⟨k, hk⟩
    obtain ⟨z, hz, he, _⟩ := finite_tail_gcd_attained hD hDH
    refine ⟨k • z, ?_, ?_⟩
    · intro j hj
      simp [Finsupp.smul_apply, hz j hj]
    · rw [channelSynthesis_smul, Finsupp.smul_apply, smul_eq_mul, he, hk]
      ring



lemma attainsMoment_iff_support_divisibility {D H : ℕ}
    (hD : 2 ≤ D) (hDH : D < H)
    (hG : IsScalarTailGcd D (finiteScalarGcd D H)) (m : ℤ) :
    AttainsMoment D m ↔ ∃ t : ℤ,
      m = (channelLCM D : ℤ) * t ∧ (finiteScalarGcd D H : ℤ) ∣ t * kernelOne D := by
  constructor
  · rintro ⟨f, hf, hc, hm⟩
    obtain ⟨t, z, hz, he⟩ :=
      (low_channel_classification hD f ((admissible_iff f).mp hf).1).mp hc
    have hsupport : t * kernelOne D + channelSynthesis z 1 = 0 :=
      support_equation.mp (he ▸ hf)
    have hdiv := tail_gcd_dvd_one (by omega) hG hz
    refine ⟨t, ?_, ?_⟩
    · rw [he, factorialMoment_add, factorialMoment_smul, canonicalKernel_moment,
        tail_moment (by omega) hz, add_zero] at hm
      nlinarith [hm]
    · have hneg : t * kernelOne D = -channelSynthesis z 1 := by omega
      rw [hneg]
      exact dvd_neg.mpr hdiv
  · rintro ⟨t, hm, hdiv⟩
    obtain ⟨z, hz, he⟩ := (exists_tail_one_iff (by omega) hDH hG
      (-(t * kernelOne D))).mpr (dvd_neg.mpr hdiv)
    let f := t • canonicalKernel D + channelSynthesis z
    refine ⟨f, ?_, ?_, ?_⟩
    · apply support_equation.mpr
      rw [he]
      ring
    · have hf0 : f 0 = 0 := by
        simp [f, Finsupp.add_apply, Finsupp.smul_apply,
          canonicalKernel_at_zero, synthesis_at_zero]
      exact (low_channel_classification hD f hf0).mpr ⟨t, z, hz, rfl⟩
    · dsimp [f]
      rw [factorialMoment_add, factorialMoment_smul, canonicalKernel_moment,
        tail_moment (by omega) hz, add_zero, hm]
      ring
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) (m : ℤ) :
    AttainsMoment D m ↔ minimumMoment D p ∣ m := by
  let H := D * (2 * p - 1)
  have hcert := finite_channel_moment_certificate hD hp hDp hpD
  have hDH : D < H := by
    have hp2 := hp.two_le
    have hp3 : 3 ≤ 2 * p - 1 := by omega
    dsimp [H]
    calc
      D < D * 3 := by omega
      _ ≤ D * (2 * p - 1) := Nat.mul_le_mul_left D hp3
  have hg : (0 : ℤ) < finiteScalarGcd D H := by exact_mod_cast hcert.1
  rw [attainsMoment_iff_support_divisibility hD hDH hcert.2.1]
  change (∃ t : ℤ, m = (channelLCM D : ℤ) * t ∧
    (finiteScalarGcd D H : ℤ) ∣ t * kernelOne D) ↔
    (channelLCM D : ℤ) * ((finiteScalarGcd D H : ℤ) /
      (Int.gcd (finiteScalarGcd D H : ℤ) (kernelOne D) : ℤ)) ∣ m
  constructor
  · rintro ⟨t, hm, ht⟩
    obtain ⟨k, hk⟩ := (gcd_quotient_dvd_iff _ _ t hg).mpr ht
    refine ⟨k, ?_⟩
    rw [hm, hk]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨((finiteScalarGcd D H : ℤ) /
      (Int.gcd (finiteScalarGcd D H : ℤ) (kernelOne D) : ℤ)) * k, ?_, ?_⟩
    · rw [hk]
      ring
    · exact (gcd_quotient_dvd_iff _ _ _ hg).mp (dvd_mul_right _ _)
