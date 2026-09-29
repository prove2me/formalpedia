-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialTruncation.capped_one_eq_binary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:46:23.779988+00:00
-- url     : https://prove2.me/submissions/c79bdc24-c6c8-43ee-86fa-589d90a3f97a

-- Sol generated from Novelty/ZeroFitDialTruncation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialTruncation
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialTruncation_capped_spearmanSq
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
    spearmanSq (capped b 1) = 3 / 4 * ((4 : ℚ) ^ b / ((4 : ℚ) ^ b - 1)) := by
  rw [capped_spearmanSq b 1 hb hb]
  have hx : (2 : ℚ) ≤ (2 : ℚ) ^ b := by
    calc (2 : ℚ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have h8 : ((2 : ℚ) ^ b) ^ 3 = 8 ^ b := pow_two_cube b
  have h4 : ((2 : ℚ) ^ b) ^ 2 = 4 ^ b := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hstep : (8 : ℚ) ^ (b - 1) = (8 : ℚ) ^ b / 8 := by
    have hb1 : b = (b - 1) + 1 := by omega
    rw [show (8 : ℚ) ^ b = 8 ^ ((b - 1) + 1) from by rw [← hb1], pow_succ]
    ring
  rw [hstep]
  set x : ℚ := (2 : ℚ) ^ b with hxdef
  have h1 : x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by intro hcon; linarith
  have hx1' : x + 1 ≠ 0 := by linarith
  have hrw8 : (8 : ℚ) ^ b = x ^ 3 := h8.symm
  have hrw4 : (4 : ℚ) ^ b = x ^ 2 := h4.symm
  rw [hrw8, hrw4]
  have hfac : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
  have hfac2 : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hfac, hfac2]
  field_simp
  ring
