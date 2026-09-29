-- Prove2me | solution 1 for AlgebraicCodingTheory.unique_decode_of_separation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:12:46.939774+00:00
-- url     : https://prove2.me/submissions/4da94e0d-d180-4f76-8fea-111d018e5833

-- Sol generated from Cryptography/AlgebraicCodingTheory.lean
import Mathlib
import Definitions.Def_Cryptography_AlgebraicCodingTheory

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
theorem solution{α : Type*} [DecidableEq α] {n d t : ℕ}
    (x y received : Fin n → α) (hsep : d ≤ hammingDistance x y)
    (hx : hammingDistance x received ≤ t)
    (hy : hammingDistance y received ≤ t)
    (hradius : 2 * t < d) : False := by
  -- Triangle inequality: dist x y ≤ dist x received + dist received y
  have htri : hammingDistance x y ≤ hammingDistance x received + hammingDistance received y := by
    unfold hammingDistance
    have hsub : Finset.univ.filter fun i => x i ≠ y i ⊆
                (Finset.univ.filter fun i => x i ≠ received i) ∪
                (Finset.univ.filter fun i => received i ≠ y i) := by
      intro i hi
      simp at hi
      have : x i ≠ received i ∨ received i ≠ y i := by
        by_contra hne
        push_neg at hne
        exact hi (hne.1.trans hne.2)
      simp [this]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- Symmetry: dist y received = dist received y
  have hsym : hammingDistance y received = hammingDistance received y := by
    unfold hammingDistance
    congr 1
    apply Finset.filter_congr
    intro i _
    exact ne_comm
  omega
