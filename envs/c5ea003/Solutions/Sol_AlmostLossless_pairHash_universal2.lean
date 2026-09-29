-- Prove2me | solution 1 for AlmostLossless.pairHash_universal2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:29.915669+00:00
-- url     : https://prove2.me/submissions/c0d15a85-4509-4b24-9c03-a8f98d93fc22

-- Sol generated from Bridges/AlmostLosslessChecksum.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessChecksum
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression V: Checksums and Guaranteed Error Detection

## Bridge: Product constructions (combinatorics) ↔ Error detection (coding theory)

`AlmostLosslessRandomCoding` shows that a codebook symbol is *never* corrupted
silently, and that an off-codebook symbol is corrupted with probability at most
`|S|/M`.  A **checksum** is the standard way to push the latter down without
redesigning the code: append `log C` extra bits computed by a second,
independent universal family.

The structural fact that makes this work is that 2-universality is closed under
pairing, with the collision parameter *multiplying*:

  `pairHash_universal2 : Universal2 H → Universal2 G → Universal2 (H ⊗ G)`

where `H ⊗ G` has `K·K'` keys and `M·C` codewords.  Feeding this into the main
achievability theorem gives `exists_checksummed_scheme`: silent corruption below
any target `η`, at an additive cost of `log C` bits.

## Impact: guaranteed_error_detection, no_silent_corruption
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K K' M C : ℕ}


omit [Fintype α] [DecidableEq α] in
theorem pairHash_eq_iff {H : Fin K → α → Fin M} {G : Fin K' → α → Fin C}
    {k : Fin (K * K')} {x y : α} :
    pairHash H G k x = pairHash H G k y ↔
      (H (finProdFinEquiv.symm k).1 x = H (finProdFinEquiv.symm k).1 y
        ∧ G (finProdFinEquiv.symm k).2 x = G (finProdFinEquiv.symm k).2 y) := by
  unfold pairHash
  rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]






open AlmostLossless in
omit [Fintype α] [DecidableEq α] in
theorem solution{H : Fin K → α → Fin M} {G : Fin K' → α → Fin C}
    (hH : Universal2 H) (hG : Universal2 G) : Universal2 (pairHash H G) := by
  classical
  intro x y hxy
  -- transport the key set along the product equivalence
  have hcard : (Finset.univ.filter (fun k : Fin (K * K') =>
        pairHash H G k x = pairHash H G k y)).card
      = (Finset.univ.filter (fun k : Fin K => H k x = H k y)).card
        * (Finset.univ.filter (fun k : Fin K' => G k x = G k y)).card := by
    have h1 : (Finset.univ.filter (fun k : Fin (K * K') =>
          pairHash H G k x = pairHash H G k y)).card
        = (Finset.univ.filter (fun kk : Fin K × Fin K' =>
            H kk.1 x = H kk.1 y ∧ G kk.2 x = G kk.2 y)).card := by
      refine Finset.card_equiv finProdFinEquiv.symm ?_
      intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairHash_eq_iff]
    have h2 : (Finset.univ.filter (fun kk : Fin K × Fin K' =>
          H kk.1 x = H kk.1 y ∧ G kk.2 x = G kk.2 y))
        = (Finset.univ.filter (fun k : Fin K => H k x = H k y))
            ×ˢ (Finset.univ.filter (fun k : Fin K' => G k x = G k y)) := by
      ext kk
      simp [Finset.mem_product]
    rw [h1, h2, Finset.card_product]
  have hMC : (0 : ℝ) ≤ (M : ℝ) * C := by positivity
  have h1 := hH x y hxy
  have h2 := hG x y hxy
  have hn1 : (0 : ℝ) ≤ ((Finset.univ.filter (fun k : Fin K => H k x = H k y)).card : ℝ) :=
    Nat.cast_nonneg _
  have hn2 : (0 : ℝ) ≤ ((Finset.univ.filter (fun k : Fin K' => G k x = G k y)).card : ℝ) :=
    Nat.cast_nonneg _
  have hK1 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  calc ((Finset.univ.filter (fun k : Fin (K * K') =>
          pairHash H G k x = pairHash H G k y)).card : ℝ) * (M * C : ℕ)
      = (((Finset.univ.filter (fun k : Fin K => H k x = H k y)).card : ℝ) * M)
          * (((Finset.univ.filter (fun k : Fin K' => G k x = G k y)).card : ℝ) * C) := by
        rw [hcard]; push_cast; ring
    _ ≤ (K : ℝ) * (K' : ℝ) := mul_le_mul h1 h2 (by positivity) hK1
    _ = ((K * K' : ℕ) : ℝ) := by push_cast; ring
