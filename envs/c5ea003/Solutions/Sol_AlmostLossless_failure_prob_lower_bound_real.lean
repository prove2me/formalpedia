-- Prove2me | solution 1 for AlmostLossless.failure_prob_lower_bound_real
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:40:46.808355+00:00
-- url     : https://prove2.me/submissions/f76c8151-b10d-46be-93cf-1f00c3adf42a

-- Sol generated from Geometry/AlmostLosslessConverse.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_failure_prob_lower_bound
/-
# How far beyond the pigeonhole bound can one go?  Converse and tightness

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

Two adversarial questions about the almost-lossless scheme of
`Geometry.AlmostLosslessDecoder`:

1. *How much can the counting bound really be relaxed?*
   `AlmostLossless.converse_card_good_le` — **the ε-relaxed pigeonhole bound**:
   for **any** encoder/decoder pair whatsoever, the set of strings decoded
   correctly has size at most `M`.  So a `(1-ε)`-reliable code for a typical set
   `S` still needs `M ≥ (1-ε)|S|`: relaxation buys a factor `(1-ε)`, no more.

2. *Is the `1/ε` overhead of random hashing an artefact of the union bound?*
   No.  `AlmostLossless.failure_prob_lower_bound` is a **Bonferroni lower bound**
   on the failure probability of uniform random hashing:
   `P[failure] ≥ (|S|-1) / (2M)` once `2(|S|-2) ≤ M`.
   Hence uniform random hashing genuinely needs `M ≳ |S| / ε`, a factor `Θ(1/ε)`
   above the converse — the gap is a property of the *random codebook*, not of
   the analysis.

Supporting combinatorics proved here from scratch:
* `AlmostLossless.card_sum_le_card_biUnion_add_offDiag` — the second Bonferroni
  inequality for an arbitrary finite family of finite sets.
* `AlmostLossless.card_doubleCollision_mul_le` — a two-coordinate refinement of
  the marginal count of `AlmostLosslessCore`: two prescribed collisions have
  probability `1/M²`.
-/

open AlmostLossless

open Finset

/-! ## 1. The ε-relaxed pigeonhole bound (converse) -/



/-! ## 2. Bonferroni: a lower bound for unions of finite sets -/


/-! ## 3. Two prescribed collisions have probability `1/M²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-! ## 4. The failure probability of random hashing is genuinely `≍ |S|/M` -/

variable {α : Type*} [Fintype α] [DecidableEq α]





open AlmostLossless in
theorem solution(S : Finset α) (x : α) (hM : 0 < M)
    (hk : 2 * ((S.erase x).card - 1) ≤ M) :
    ((S.erase x).card : ℝ) / (2 * M)
      ≤ ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by
  classical
  set k := (S.erase x).card with hk'
  set N := (M : ℝ) ^ Fintype.card α with hN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hbase := failure_prob_lower_bound (M := M) S x
  have hoff : (S.erase x).offDiag.card = k * k - k := by
    rw [Finset.offDiag_card]
  rw [hoff] at hbase
  -- cast to ℝ
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · have hkk : (k : ℝ) * k - k = ((k * k - k : ℕ) : ℝ) := by
      have : k ≤ k * k := Nat.le_mul_of_pos_left k hkpos
      push_cast [Nat.cast_sub this]
      ring
    have hbase' : (k : ℝ) * M * N
        ≤ (M : ℝ) ^ 2 * (failSet S x M).card + ((k : ℝ) * k - k) * N := by
      have h := (Nat.cast_le (α := ℝ)).2 hbase
      push_cast at h
      rw [hkk]
      convert h using 2
    -- `2(k-1) ≤ M` gives `k(k-1) ≤ kM/2`
    have hkM : 2 * ((k : ℝ) - 1) ≤ M := by
      have h1 : ((2 * (k - 1) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
      have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hkpos
        push_cast [Nat.cast_sub this]; ring
      push_cast [h2] at h1
      linarith
    have hcross : ((k : ℝ) * k - k) * N ≤ (k : ℝ) * M * N / 2 := by
      have h1 : (k : ℝ) * ((k : ℝ) - 1) ≤ (k : ℝ) * ((M : ℝ) / 2) := by
        have hknn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      nlinarith [hNpos.le]
    have hFN : (k : ℝ) * M * N / 2 ≤ (M : ℝ) ^ 2 * (failSet S x M).card := by
      linarith
    rw [div_le_div_iff₀ (by positivity) hNpos]
    nlinarith [hFN, hNpos, hMpos]
