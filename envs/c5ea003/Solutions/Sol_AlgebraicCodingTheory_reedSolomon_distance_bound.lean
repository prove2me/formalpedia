-- Prove2me | solution 1 for AlgebraicCodingTheory.reedSolomon_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:12:46.272086+00:00
-- url     : https://prove2.me/submissions/5ee164c1-7dab-43c9-8dc6-da5eef209702

-- Sol generated from Cryptography/AlgebraicCodingTheory.lean
import Mathlib
import Definitions.Def_Cryptography_AlgebraicCodingTheory
import Theorems.Thm_AlgebraicCodingTheory_reedSolomon_weight_bound

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
    (hpoints : Function.Injective points) (p q : F[X]) (hpq : p ≠ q)
    (hpdeg : p.natDegree < k) (hqdeg : q.natDegree < k) (hkn : k ≤ n) :
    n - k + 1 ≤ hammingDistance (reedSolomonEval points p) (reedSolomonEval points q) := by
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hdeg : (p - q).natDegree < k := by
    calc (p - q).natDegree ≤ max p.natDegree q.natDegree := Polynomial.natDegree_sub_le p q
      _ < k := max_lt hpdeg hqdeg
  have hbound := reedSolomon_weight_bound points hpoints (p - q) hdiff hdeg hkn
  simp only [hammingDistance, reedSolomonEval] at hbound ⊢
  convert hbound using 2
  simp [Polynomial.eval_sub]
  apply Finset.filter_congr
  intro i _
  simp [sub_eq_zero]
