-- Prove2me | solution 1 for AlmostLossless.failure_prob_exact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:35:56.852613+00:00
-- url     : https://prove2.me/submissions/89c3d93e-f6e7-4a1a-8561-698ee0bcff16

-- Sol generated from Geometry/AlmostLosslessExact.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_AlmostLosslessExact
import Theorems.Thm_AlmostLossless_card_codebooks
import Theorems.Thm_AlmostLossless_card_sepSet
/-
# The exact failure probability of random hashing

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`AlmostLosslessDecoder` gives the upper bound `P[failure] ≤ (|S|-1)/M` and
`AlmostLosslessConverse` the Bonferroni lower bound `P[failure] ≥ (|S|-1)/(2M)`.
Here we compute the quantity **exactly**:

`AlmostLossless.card_sepSet` :  `M^k · |{H : H separates x from D}| = (M-1)^k · M^{|α|}`  (`k = |D|`),

whence `AlmostLossless.failure_prob_exact`:

`P[failure at x] = 1 - (1 - 1/M)^{|S|-1}`.

Both previously proved bounds are corollaries of this identity in the regime
they cover, and the measured values of `AlmostLosslessLabNotes` (`3/4`, `5/9`,
`7/16`, `15/64`, `31/256`) are exactly its values at `|S| = 3`.

The proof is an explicit bijection
`{H separating x from D ∪ {a}} × Fin M  ≃  Σ_{H separating x from D} (Fin M \ {H x})`,
given by `(H, v) ↦ ⟨update H a v, H a⟩`, iterated by induction on `D`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}




/-- The separating codebooks are exactly the complement of the failure event. -/
theorem sepSet_compl (S : Finset α) (x : α) :
    sepSet (S.erase x) x M = (failSet S x M)ᶜ := by
  ext H
  simp only [sepSet, failSet, mem_filter, mem_univ, true_and, mem_compl, not_exists]
  push_neg
  rfl

/-- **Exact failure count of uniform random hashing**:
`M^k · (M^{|α|} - |failSet|) = (M-1)^k · M^{|α|}` with `k = |S| - 1`. -/
theorem card_failSet_exact (S : Finset α) (x : α) :
    M ^ (S.erase x).card * (M ^ Fintype.card α - (failSet S x M).card)
      = (M - 1) ^ (S.erase x).card * M ^ Fintype.card α := by
  have hx : x ∉ S.erase x := Finset.notMem_erase x S
  have h := card_sepSet (M := M) x (S.erase x) hx
  rw [sepSet_compl] at h
  rwa [Finset.card_compl, card_codebooks] at h



open AlmostLossless in
theorem solution(S : Finset α) (x : α) (hM : 0 < M) :
    ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α)
      = 1 - (1 - 1 / (M : ℝ)) ^ (S.erase x).card := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hpow : (0 : ℝ) < (M : ℝ) ^ Fintype.card α := by positivity
  have hkpow : (0 : ℝ) < (M : ℝ) ^ (S.erase x).card := by positivity
  have hle : (failSet S x M).card ≤ M ^ Fintype.card α := by
    have h := Finset.card_le_univ (failSet S x M)
    rwa [card_codebooks] at h
  have hnat := card_failSet_exact (M := M) S x
  -- cast the natural-number identity to ℝ
  have hcast : (M : ℝ) ^ (S.erase x).card
        * ((M : ℝ) ^ Fintype.card α - ((failSet S x M).card : ℝ))
      = ((M : ℝ) - 1) ^ (S.erase x).card * (M : ℝ) ^ Fintype.card α := by
    have h1 : (((M ^ (S.erase x).card * (M ^ Fintype.card α - (failSet S x M).card) : ℕ)) : ℝ)
        = (((M - 1) ^ (S.erase x).card * M ^ Fintype.card α : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hnat
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have : (1 : ℕ) ≤ M := hM
      push_cast [Nat.cast_sub this]; ring
    push_cast [Nat.cast_sub hle, hM1] at h1
    exact h1
  have hsplit : (1 - 1 / (M : ℝ)) ^ (S.erase x).card
      = ((M : ℝ) - 1) ^ (S.erase x).card / (M : ℝ) ^ (S.erase x).card := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [hsplit]
  field_simp
  nlinarith [hcast, hkpow, hpow]
