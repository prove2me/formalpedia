-- Prove2me | solution 1 for AlgebraicCodingTheory.reedSolomon_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:11:36.941747+00:00
-- url     : https://prove2.me/submissions/30d7c088-7b1b-491b-85c7-bce50d99d4e8

-- Sol generated from Cryptography/AlgebraicCodingTheory.lean
import Mathlib
import Definitions.Def_Cryptography_AlgebraicCodingTheory
import Theorems.Thm_AlgebraicCodingTheory_card_zero_evaluations_le_natDegree

/-!
# Reed–Solomon codes over finite fields

This file gives a direct polynomial-evaluation construction of Reed–Solomon codes and
proves their designed-distance bound.  It also derives injectivity, separation, and a
unique-decoding theorem from the bound.
-/

open AlgebraicCodingTheory

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]










open AlgebraicCodingTheory in
theorem solution{n k : ℕ} (points : Fin n → F)
    (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0)
    (hdeg : p.natDegree < k) (hkn : k ≤ n) :
    n - k + 1 ≤ (Finset.univ.filter fun i => reedSolomonEval points p i ≠ 0).card := by
  have hzero := card_zero_evaluations_le_natDegree points hpoints p hp
  -- reedSolomonEval points p i = p.eval (points i)
  have heq : ∀ i, reedSolomonEval points p i = p.eval (points i) := fun i => rfl
  -- The nonzero and zero sets partition Fin n
  have hcard_sum : (Finset.univ.filter fun i => p.eval (points i) ≠ 0).card +
                   (Finset.univ.filter fun i => p.eval (points i) = 0).card = n := by
    have : (Finset.univ.filter fun i => p.eval (points i) ≠ 0) ∪
           (Finset.univ.filter fun i => p.eval (points i) = 0) = Finset.univ := by
      ext i; by_cases hi : p.eval (points i) = 0 <;> simp [hi]
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ _ => by tauto), this]
    simp
  -- zeros ≤ p.natDegree < k implies zeros ≤ k - 1
  have hzero_lt_k : (Finset.univ.filter fun i => p.eval (points i) = 0).card < k := by
    calc (Finset.univ.filter fun i => p.eval (points i) = 0).card
        ≤ p.natDegree := hzero
      _ < k := hdeg
  -- nonzeros = n - zeros ≥ n - (k - 1) = n - k + 1
  have hnonzero_le : (Finset.univ.filter fun i => p.eval (points i) ≠ 0).card =
                     n - (Finset.univ.filter fun i => p.eval (points i) = 0).card := by
    omega
  simp only [reedSolomonEval]
  rw [hnonzero_le]
  omega
