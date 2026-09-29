-- Prove2me | solution 1 for AlmostLossless.linHash_universal2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:28.700982+00:00
-- url     : https://prove2.me/submissions/e1df87df-bc00-4878-94ac-f9fab79b1964

-- Sol generated from Bridges/AlmostLosslessLinearHash.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression IV: An Explicit 2-Universal Family

## Bridge: Finite fields (algebra) ↔ Shannon random coding (probability)

The achievability theorem of `AlmostLosslessRandomCoding` is stated for an
abstract 2-universal family.  This file removes any suspicion of vacuity by
exhibiting one: the **inner-product family** over a prime field,

  `h_k(x₁, x₂) = x₁ + k·x₂`  on  `(ZMod p)²`,  keyed by `k ∈ Fin p`.

It compresses a source of `p²` symbols into `p` codewords (half the raw rate),
and `linHash_universal2` proves the 2-universal property: two distinct source
symbols collide for **at most one** of the `p` keys.  Instantiating the general
theorem gives `exists_linear_almost_lossless`: a completely explicit
almost-lossless compressor with a proved failure bound and a proved decoding
cost.

## Impact: explicit_almost_lossless_code, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable (p : ℕ) [Fact p.Prime]


theorem keyVal_injective : Function.Injective (keyVal p) := by
  intro k k' h
  unfold keyVal at h
  have h1 : ((k.val : ℕ) : ZMod p).val = k.val := ZMod.val_cast_of_lt k.isLt
  have h2 : ((k'.val : ℕ) : ZMod p).val = k'.val := ZMod.val_cast_of_lt k'.isLt
  exact Fin.ext (by rw [← h1, ← h2, h])


theorem linHash_eq_iff {k : Fin p} {x y : ZMod p × ZMod p} :
    linHash p k x = linHash p k y ↔
      x.1 + keyVal p k * x.2 = y.1 + keyVal p k * y.2 := by
  unfold linHash
  rw [Fin.mk.injEq]
  exact ⟨fun h => ZMod.val_injective p h, fun h => by rw [h]⟩





/-! ## A concrete instance with explicit figures -/







open AlmostLossless in
theorem solution: Universal2 (linHash p) := by
  intro x y hxy
  have hcard : (Finset.univ.filter (fun k => linHash p k x = linHash p k y)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k1 h1 k2 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, linHash_eq_iff] at h1 h2
    have e3 : (keyVal p k1 - keyVal p k2) * (x.2 - y.2) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp e3 with h | h
    · exact keyVal_injective p (sub_eq_zero.mp h)
    · exfalso
      have hx2 : x.2 = y.2 := sub_eq_zero.mp h
      have hx1 : x.1 = y.1 := by
        rw [hx2] at h1; linear_combination h1
      exact hxy (Prod.ext hx1 hx2)
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hc : ((Finset.univ.filter (fun k => linHash p k x = linHash p k y)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  calc ((Finset.univ.filter (fun k => linHash p k x = linHash p k y)).card : ℝ) * p
      ≤ 1 * p := by nlinarith
    _ = (p : ℝ) := one_mul _
