-- Prove2me | solution 1 for AlmostLossless.powDist_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:56:57.248977+00:00
-- url     : https://prove2.me/submissions/b863eb2e-4f3b-453e-a449-ce2068aa11fd

-- Sol generated from Bridges/AlmostLosslessBlockDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_powDist_marginal
import Theorems.Thm_AlmostLossless_setMass_biUnion_le
import Theorems.Thm_AlmostLossless_setMass_mono
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
theorem solution(μ : FinProbDist β) (b : ℕ) (Bs : Fin b → Finset β) :
    setMass (powDist μ b) (Finset.univ.filter (fun x : Fin b → β => ∃ j, x j ∈ Bs j))
      ≤ ∑ j, setMass μ (Bs j) := by
  classical
  have hsub : Finset.univ.filter (fun x : Fin b → β => ∃ j, x j ∈ Bs j)
      ⊆ Finset.univ.biUnion
          (fun j => Finset.univ.filter (fun x : Fin b → β => x j ∈ Bs j)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [hj]⟩
  refine le_trans (setMass_mono _ hsub) ?_
  refine le_trans (setMass_biUnion_le _ _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => powDist_marginal μ b j (Bs j)
