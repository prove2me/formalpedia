-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialTruncation.capped_tieCorr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:43:01.314701+00:00
-- url     : https://prove2.me/submissions/fbb4359b-69ac-433b-88d4-2c3264a1fcfa

-- Sol generated from Novelty/ZeroFitDialTruncation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialTruncation
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_pow_two_cube
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_tieCorr_cons

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
theorem solution: ∀ (m c : ℕ), c ≤ m →
    12 * tieCorr (capped m c) = ((8 : ℚ) ^ m + 6 * 8 ^ (m - c)) / 7 - 2 ^ m := by
  intro m c
  induction c generalizing m with
  | zero =>
      intro _
      have hnil : tieCorr ([] : List ℕ) = 0 := rfl
      rw [capped, tieCorr_cons, hnil, Nat.sub_zero]
      push_cast
      rw [pow_two_cube m]
      ring
  | succ c ih =>
      intro h
      match m with
      | 0 => omega
      | m + 1 =>
          have hc : c ≤ m := by omega
          have hsub : m + 1 - (c + 1) = m - c := by omega
          rw [capped, tieCorr_cons, mul_add, ih m hc, hsub]
          push_cast
          have h8 : ((2 : ℚ) ^ m) ^ 3 = 8 ^ m := pow_two_cube m
          rw [pow_succ (8 : ℚ) m, pow_succ (2 : ℚ) m]
          linarith [h8]
