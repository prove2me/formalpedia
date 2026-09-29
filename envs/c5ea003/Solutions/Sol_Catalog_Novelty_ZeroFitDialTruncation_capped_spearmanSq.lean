-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialTruncation.capped_spearmanSq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:44:42.030381+00:00
-- url     : https://prove2.me/submissions/d926f729-2b05-4564-b69e-10243663aa52

-- Sol generated from Novelty/ZeroFitDialTruncation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialTruncation
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialTruncation_capped_sum
import Theorems.Thm_Catalog_Novelty_ZeroFitDialTruncation_capped_tieCorr
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_cube_sub_self_pos
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_pow_two_cube
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_spearmanSq_eq

/-!
# Truncated zero-count statistics cannot explain the U64 dial

Cycle 3 of the round-61 investigation.

Cycle 1 (`Novelty.ZeroFitDialU64`) showed that the *full* 2-adic tie profile has ceiling
`ρ² → 6/7`, far above the recorded `ρ² = 0.419904`, and that the ceiling is essentially
constant in the bitlen.  A natural rescue for a "the statistic is to blame" explanation is
**truncation**: real instrumentation caps the trailing-zero count at some `c`, merging all
draws with `v₂ ≥ c` (and the draw `0`) into one big block.  Since a big block destroys a lot
of rank variance, one might hope that a small cap explains the low reading.

This file computes that ceiling exactly and refutes the hope:

`ρ²(b, c) = (6/7) · (8^b − 8^{b−c}) / (8^b − 2^b)`  (`capped_spearmanSq`)

which is **increasing in the cap** and bounded below by `3/4` for every cap `c ≥ 1`
(`capped_ge_three_quarters`).  Since the recorded pooled reading is `ρ² = 0.419904 < 3/4`,
*no* truncation of the zero-count statistic can produce it (`no_truncation_explains_u64`).

Two consistency checks fall out.  At `c = 1` the profile is the even/odd split and the
formula gives `(3/4)·2^{2b}/(2^{2b} − 1)`, matching the balanced two-class value
`3jk/((j+k)² − 1)` of `Novelty.ZeroFitDialNested`.  At `c = b` it reproduces the full
dyadic ceiling of cycle 1.

Conclusion of the three cycles: the decline of the zero-fit dial is a property of the
*response*, not of the zero-count statistic, however that statistic is quantised.
-/

open Finset

open Catalog.Novelty.ZeroFitDialTruncation

open Catalog.Novelty.ZeroFitDialU64










open Catalog.Novelty.ZeroFitDialTruncation in
theorem solution(b c : ℕ) (hc : c ≤ b) (hb : 1 ≤ b) :
    spearmanSq (capped b c) = (6 / 7) * ((8 : ℚ) ^ b - 8 ^ (b - c)) / ((8 : ℚ) ^ b - 2 ^ b) := by
  have hsum : (capped b c).sum = 2 ^ b := capped_sum b c hc
  have h2 : 2 ≤ (capped b c).sum := by
    rw [hsum]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hx : (2 : ℚ) ≤ (2 : ℚ) ^ b := by
    calc (2 : ℚ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have hcast : (((capped b c).sum : ℕ) : ℚ) = (2 : ℚ) ^ b := by rw [hsum]; push_cast; ring
  have h8 : ((2 : ℚ) ^ b) ^ 3 = 8 ^ b := pow_two_cube b
  rw [spearmanSq_eq _ h2, hcast, capped_tieCorr b c hc, h8]
  have hden : ((8 : ℚ) ^ b - 2 ^ b) ≠ 0 := by
    have : (0 : ℚ) < ((2 : ℚ) ^ b) ^ 3 - 2 ^ b := cube_sub_self_pos hx
    rw [h8] at this
    exact ne_of_gt this
  field_simp
  ring
