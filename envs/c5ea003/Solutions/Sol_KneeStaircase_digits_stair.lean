-- Prove2me | solution 1 for KneeStaircase.digits_stair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:48:57.289615+00:00
-- url     : https://prove2.me/submissions/031e1a02-2359-473f-9739-79d248aa892d

-- Sol generated from NumberTheory/KneeStaircaseArithmetic.lean
import Mathlib
import Definitions.Def_NumberTheory_KneeStaircaseArithmetic
import Theorems.Thm_KneeStaircase_digits_two_pow_sub_one
import Theorems.Thm_KneeStaircase_stair_pos
/-
# Binary staircase numbers: the arithmetic of the NET-47 knee spread

The NET-47 round reports, at the cell `(d = 4, ctx = 1024)`, the three-seed knee distribution

```
{96, 112, 128},   product point  d·ctx/32 = 128 = 2^7,
```

with the "7/8 median law" `112 = (7/8)·128` and a "±16 half-grid-step jitter".  Written in base
two the three numbers are `1100000`, `1110000`, `10000000`: each is a block of ones followed by a
block of zeros.  This file isolates that combinatorial shape as a number-theoretic object,

```
stair b j = 2 ^ b * (2 ^ j - 1) = 2 ^ (b + j) - 2 ^ b,
```

the *binary staircase number* with `j` ones and `b` trailing zeros, and proves the arithmetic
which makes the measured pattern forced rather than accidental.

Main results.

* `KneeStaircase.digits_stair` — the defining combinatorial description: the base-2 digits of
  `stair b j` are `b` zeros followed by `j` ones.  Hence `stair` is a *normal form*:
  `KneeStaircase.stair_injective2` shows `(b, j)` is recoverable from the number, via the 2-adic
  valuation (`KneeStaircase.factorization_two_stair`) and the digit sum
  (`KneeStaircase.digit_sum_stair`).
* `KneeStaircase.two_mul_stair_succ` — the **midpoint law**
  `2 · stair b (j+1) = stair (b+1) j + 2 ^ (b+j+1)`: every rung of the ladder is the exact
  midpoint of the previous rung and the top point `2^n`.  This is the abstract form of
  `2 · 112 = 96 + 128`.
* `KneeStaircase.ladder_arithmetic_progression` — consequently the triple
  `(stair (b+1) j, stair b (j+1), 2^(b+j+1))` is an arithmetic progression of common difference
  `2 ^ b`: a knee spread of this shape has mean = median, and the median is the `(2^{j+1}-1)/2^{j+1}`
  fraction of the top point.
* `KneeStaircase.stair_lt_two_pow`, `KneeStaircase.stair_strictMono_ones` — the ladder increases
  in `j` and stays strictly below the top point: the product point is the maximum of the family,
  never attained by a genuine staircase rung.
* `KneeStaircase.net47_*` — the instantiation at the measured numbers: `96 = stair 5 2`,
  `112 = stair 4 3`, `128 = 2^7`, `8·112 = 7·128`, and the arithmetic-progression statement of the
  jitter, all as consequences of the general lemmas rather than by evaluation.

Companion file: `Catalog/NumberTheory/KneeStaircaseDivisorSpectrum.lean` (divisor sums, the
abundant/deficient/perfect classification of the family and its analytic limit).
-/


open KneeStaircase

/-! ## 1.  The staircase family -/










/-! ## 2.  The midpoint (half-step) law -/




/-! ## 3.  Base-two digits: the staircase is a normal form -/




/-! ## 4.  The 2-adic valuation and injectivity of the parametrisation -/




/-! ## 5.  The NET-47 instance -/





/-! ### The window `(96, 128)`: why the mid-grid read is forced -/









open KneeStaircase in
theorem solution{b j : ℕ} (hj : 1 ≤ j) :
    Nat.digits 2 (stair b j) = List.replicate b 0 ++ List.replicate j 1 := by
  induction b with
  | zero => simpa [stair] using digits_two_pow_sub_one j
  | succ n ih =>
      have hpos : 0 < stair (n + 1) j := stair_pos hj
      rw [Nat.digits_def' (by norm_num) hpos]
      have hs : stair (n + 1) j = 2 * stair n j := by
        simp [stair, pow_succ]; ring
      have h1 : stair (n + 1) j % 2 = 0 := by omega
      have h2 : stair (n + 1) j / 2 = stair n j := by omega
      rw [h1, h2, ih, List.replicate_succ]
      simp
