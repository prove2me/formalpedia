-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialTruncation.capped_full_eq_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:46:21.616597+00:00
-- url     : https://prove2.me/submissions/a0beff30-46fd-4af6-b2fe-9fe6070095ba

-- Sol generated from Novelty/ZeroFitDialTruncation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialTruncation
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialTruncation_capped_spearmanSq
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_dyadic_spearmanSq
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_pow_two_cube

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
theorem solution(b : ℕ) (hb : 1 ≤ b) :
    spearmanSq (capped b b) = spearmanSq (dyadicBlocks b) := by
  rw [capped_spearmanSq b b le_rfl hb, dyadic_spearmanSq b hb, Nat.sub_self, pow_zero]
  have hx : (2 : ℚ) ≤ (2 : ℚ) ^ b := by
    calc (2 : ℚ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have h8 : ((2 : ℚ) ^ b) ^ 3 = 8 ^ b := pow_two_cube b
  set x : ℚ := (2 : ℚ) ^ b with hxdef
  have h1 : x ≠ 0 := by linarith
  have h2 : x + 1 ≠ 0 := by linarith
  have h3 : x - 1 ≠ 0 := by intro hcon; linarith
  have hrw : (8 : ℚ) ^ b = x ^ 3 := h8.symm
  rw [hrw]
  have hfac : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
  rw [hfac]
  field_simp
  ring
