-- Prove2me | Definitions.Def_Bridges_AlmostLosslessBlockDecoding
-- name    : Bridges_AlmostLosslessBlockDecoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:30.96277+00:00
-- url     : https://prove2.me/theorems/dc52c8dc-e9d1-4cd0-a2a1-a4fabf3f47c1
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessBlockDecoding
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessBlockDecoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessBlockDecoding.lean by skeleton subtraction
import Mathlib
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

namespace AlmostLossless

/-! ## Section 1: The `b`-fold product source -/

section Product

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The `b`-fold i.i.d. product of a finite source. -/
noncomputable def powDist (μ : FinProbDist β) (b : ℕ) : FinProbDist (Fin b → β) where
  mass x := ∏ i, μ.mass (x i)
  mass_nonneg x := Finset.prod_nonneg fun i _ => μ.mass_nonneg (x i)
  mass_sum_one := by
    have h := Finset.prod_univ_sum (fun _ : Fin b => (Finset.univ : Finset β))
      (fun (_ : Fin b) (a : β) => μ.mass a)
    simp only [Fintype.piFinset_univ, μ.mass_sum_one, Finset.prod_const_one] at h
    exact h.symm



end Product

/-! ## Section 2: The coordinatewise (block) decoder -/

section Block

variable {β : Type*} [Fintype β] [DecidableEq β] {b m : ℕ}

/-- Encode each block independently. -/
def blockEnc (h : Fin b → β → Fin m) : (Fin b → β) → (Fin b → Fin m) :=
  fun x j => h j (x j)

/-- Decode each block independently; abstain unless *every* block decodes. -/
def blockDec (l : Fin b → List β) (h : Fin b → β → Fin m) (c : Fin b → Fin m) :
    Option (Fin b → β) :=
  if hall : ∀ j, (decodeList (h j) (l j) (c j)).isSome then
    some (fun j => (decodeList (h j) (l j) (c j)).get (hall j))
  else none

/-- The block compression scheme. -/
def blockScheme (l : Fin b → List β) (h : Fin b → β → Fin m) :
    Scheme (Fin b → β) (Fin b → Fin m) where
  enc := blockEnc h
  dec := blockDec l h




/-! ## Section 3: Failure probability of the block scheme -/


/-! ## Section 4: Exact decoding cost, and the exponential separation -/

/-- Total cost of block decoding: the sum of the per-block scan costs. -/
def blockScanCost (l : Fin b → List β) (h : Fin b → β → Fin m) (c : Fin b → Fin m) : ℕ :=
  ∑ j, (scanCost (h j) (c j) (l j)).2






end Block

/-! ## Section 5: The full block scheme with a universal hash family -/

section Full

variable {β : Type*} [Fintype β] [DecidableEq β] {K m : ℕ}


end Full

end AlmostLossless


