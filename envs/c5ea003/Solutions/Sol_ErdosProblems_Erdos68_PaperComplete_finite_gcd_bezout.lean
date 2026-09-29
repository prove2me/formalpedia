-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.finite_gcd_bezout
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:13.697114+00:00
-- url     : https://prove2.me/submissions/b3ac7525-219d-424a-ae6c-368e821e3101

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

   
                                                                  
                                                                              
  

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp







lemma integerEvaluation_single (w : ℕ → ℤ) (i : ℕ) (c : ℤ) :
    integerEvaluation w (single i c) = c * w i := by
  unfold integerEvaluation
  exact Finsupp.sum_single_index (by simp)

lemma integerEvaluation_add (w : ℕ → ℤ) (a b : ℕ →₀ ℤ) :
    integerEvaluation w (a + b) = integerEvaluation w a + integerEvaluation w b := by
  unfold integerEvaluation
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

lemma integerEvaluation_smul (w : ℕ → ℤ) (c : ℤ) (a : ℕ →₀ ℤ) :
    integerEvaluation w (c • a) = c * integerEvaluation w a := by
  classical
  unfold integerEvaluation
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [smul_eq_mul, mul_assoc]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (s : Finset ℕ) (w : ℕ → ℤ) :
    ∃ z : ℕ →₀ ℤ, SupportedOn z s ∧
      integerEvaluation w z = ((s.gcd (fun i => (w i).natAbs) : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · intro i hi
      rfl
    · simp [integerEvaluation]
  | @insert i s hi ih =>
    obtain ⟨z, hz, he⟩ := ih
    let g : ℕ := s.gcd (fun j => (w j).natAbs)
    let A : ℤ := Int.gcdA (w i) (g : ℤ)
    let B : ℤ := Int.gcdB (w i) (g : ℤ)
    refine ⟨single i A + B • z, ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hj (Finset.mem_insert_self i s)
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
        hji, Ne.symm hji, hz j hjs]
    · rw [integerEvaluation_add, integerEvaluation_single,
        integerEvaluation_smul, he]
      have hbez := Int.gcd_eq_gcd_ab (w i) (g : ℤ)
      have hgcd : Int.gcd (w i) (g : ℤ) =
          (insert i s).gcd (fun j => (w j).natAbs) := by
        simp [Int.gcd_def, g, Finset.gcd_insert, gcd_eq_nat_gcd]
      rw [hgcd] at hbez
      dsimp [A, B, g] at *
      nlinarith [hbez]
