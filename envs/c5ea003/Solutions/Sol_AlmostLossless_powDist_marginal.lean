-- Prove2me | solution 1 for AlmostLossless.powDist_marginal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:53:56.64246+00:00
-- url     : https://prove2.me/submissions/b7454983-ee79-411a-baaa-76824857aded

-- Sol generated from Bridges/AlmostLosslessBlockDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression III: Beating the Exponential Decoder

## Bridge: Product measures (probability) ↔ Verified algorithm cost (computation)

The naive random-coding decoder of `AlmostLosslessRandomCoding` scans the whole
codebook.  On a block source `β^b` with a typical set `T^b` the codebook has
`|T|^b` entries, so decoding is *exponential in the block length*.

This file removes that obstacle.  We decode **coordinatewise**: each of the `b`
blocks gets its own unique-match scan over the size-`|T|` codebook, and the
answers are assembled.  The results:

* `powDist_marginal` — exact marginalization for the `b`-fold product source;
* `setMass_powDist_exists_le` — a union bound over blocks for the product source;
* `blockDec_eq_some_iff` — the block decoder is *exactly* the coordinatewise
  decoder, so it never corrupts silently on the product codebook;
* `blockScheme_failure_bound` — failure probability `≤ b · (per-block failure)`;
* `blockScanCost_eq_sum` / `blockScanCost_const` — cost is exactly `b·|T|`
  hash evaluations, versus `|T|^b` for the naive scan
  (`naive_codebook_card`), and `linear_lt_pow` shows the gap is genuine.

## Impact: polynomial_time_random_coding, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

/-! ## Section 1: The `b`-fold product source -/


variable {β : Type*} [Fintype β] [DecidableEq β]





/-! ## Section 2: The coordinatewise (block) decoder -/


variable {β : Type*} [Fintype β] [DecidableEq β] {b m : ℕ}







/-! ## Section 3: Failure probability of the block scheme -/


/-! ## Section 4: Exact decoding cost, and the exponential separation -/








/-! ## Section 5: The full block scheme with a universal hash family -/


variable {β : Type*} [Fintype β] [DecidableEq β] {K m : ℕ}




open AlmostLossless in
theorem solution(μ : FinProbDist β) (b : ℕ) (j : Fin b) (B : Finset β) :
    setMass (powDist μ b) (Finset.univ.filter (fun x : Fin b → β => x j ∈ B))
      = setMass μ B := by
  classical
  have key : ∀ x : Fin b → β,
      (if x j ∈ B then ∏ i, μ.mass (x i) else 0)
        = ∏ i, (if i = j then (if x i ∈ B then μ.mass (x i) else 0) else μ.mass (x i)) := by
    intro x
    have hR : ∏ i, (if i = j then (if x i ∈ B then μ.mass (x i) else 0) else μ.mass (x i))
        = (∏ i ∈ Finset.univ.erase j, μ.mass (x i))
            * (if x j ∈ B then μ.mass (x j) else 0) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), if_pos rfl]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by
        rw [if_neg (Finset.mem_erase.mp hi).1]
    have hL : ∏ i, μ.mass (x i)
        = (∏ i ∈ Finset.univ.erase j, μ.mass (x i)) * μ.mass (x j) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    rw [hR, hL]
    by_cases hx : x j ∈ B
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, mul_zero]
  unfold setMass powDist
  simp only []
  rw [Finset.sum_filter]
  simp_rw [key]
  have h := Finset.prod_univ_sum (fun _ : Fin b => (Finset.univ : Finset β))
    (fun (i : Fin b) (a : β) => if i = j then (if a ∈ B then μ.mass a else 0) else μ.mass a)
  simp only [Fintype.piFinset_univ] at h
  have hone : ∏ i ∈ Finset.univ.erase j,
      (∑ a : β, if i = j then (if a ∈ B then μ.mass a else 0) else μ.mass a) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [if_neg (Finset.mem_erase.mp hi).1]
    exact μ.mass_sum_one
  rw [← h, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), hone, one_mul]
  simp
