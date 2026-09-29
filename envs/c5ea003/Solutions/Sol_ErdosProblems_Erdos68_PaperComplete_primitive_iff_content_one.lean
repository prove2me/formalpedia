-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.primitive_iff_content_one
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:55.615545+00:00
-- url     : https://prove2.me/submissions/9da71c67-d6aa-4421-8bae-a480f88a16ef

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

































lemma coefficientContent_dvd (f : ℕ →₀ ℤ) (n : ℕ) :
    (coefficientContent f : ℤ) ∣ f n := by
  classical
  by_cases hn : f n = 0
  · rw [hn]
    exact dvd_zero _
  · exact Int.natCast_dvd.mpr
      (Finset.gcd_dvd (f := fun j => (f j).natAbs) (Finsupp.mem_support_iff.mpr hn))

lemma coefficientContent_pos {f : ℕ →₀ ℤ} (hf : f ≠ 0) :
    0 < coefficientContent f := by
  by_contra h
  have hc : coefficientContent f = 0 := by omega
  apply hf
  ext n
  have hd := coefficientContent_dvd f n
  rw [hc, Nat.cast_zero, zero_dvd_iff] at hd
  simpa using hd
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {f : ℕ →₀ ℤ} (hf : f ≠ 0) :
    PrimitiveVector f ↔ coefficientContent f = 1 := by
  classical
  constructor
  · intro hp
    have hcpos := coefficientContent_pos hf
    by_contra hne
    have hc2 : 2 ≤ coefficientContent f := by omega
    let g : ℕ →₀ ℤ := Finsupp.mapRange
      (fun z : ℤ => z / (coefficientContent f : ℤ)) (by simp) f
    apply hp (coefficientContent f) hc2
    refine ⟨g, ?_⟩
    ext n
    simp only [Finsupp.smul_apply, smul_eq_mul]
    change f n = (coefficientContent f : ℤ) *
      (f n / (coefficientContent f : ℤ))
    exact (Int.mul_ediv_cancel' (coefficientContent_dvd f n)).symm
  · intro hc k hk
    rintro ⟨g, he⟩
    have hd : k ∣ coefficientContent f := by
      apply Finset.dvd_gcd
      intro n hn
      apply Int.natCast_dvd.mp
      refine ⟨g n, ?_⟩
      simp [he, Finsupp.smul_apply, smul_eq_mul]
    rw [hc] at hd
    have hkle := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hd
    omega
