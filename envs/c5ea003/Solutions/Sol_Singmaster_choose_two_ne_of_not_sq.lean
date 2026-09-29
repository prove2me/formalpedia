-- Prove2me | solution 1 for Singmaster.choose_two_ne_of_not_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:09:37.890088+00:00
-- url     : https://prove2.me/submissions/1d81c18c-24c6-4e21-98cd-5e118ffbf9c3

-- Sol generated from Combinatorics/SingmasterCentralBinomialExtended.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
/-
# A cubic search window: `N(C(2m,m)) = 3` up to `m = 20`, and no fives or sevens below
# `538257874440`

Sixth research cycle.  `Combinatorics.SingmasterCentralBinomial` reduced the open
question *"does any number occur exactly five or exactly seven times?"* to the single
sequence of central binomial coefficients and made the reduction effective: for
`t = C(2m,m)` the multiplicity is `3` as soon as no interior entry `C(n,k) = t` occurs
in a row `2m < n < N` with `N ≈ √(2t)` and `2 ≤ k ≤ n/2`.  Executing that quadratic
search cost `(N - 2m) · (N/2)` kernel tests and stopped at `m = 10`.

This file removes both factors of the search box.

## Two structural reductions

* **The column collapse** (`Singmaster.column_lt_of_choose_eq_centralBinom`).  In the
  escape window the column index is *tiny*: if `2k ≤ n`, `n > 2m` and
  `C(n,k) = C(2m,m)`, then `k < m`.  Indeed `C(2k,k) ≤ C(n,k)` (monotonicity in the
  row) and `m ↦ C(2m,m)` is strictly increasing, so `k ≥ m` would force
  `C(2m,m) ≤ C(2k,k) ≤ C(n,k) = C(2m,m)` with a strict inequality somewhere (from
  `k > m`, or from `n > 2m` when `k = m`).  So the columns run over `[3, m-1]`, a strip
  of height `m`, instead of a triangle of height `N/2`.

* **The triangular obstruction** (`Singmaster.choose_two_ne_of_not_sq`).  The column
  `k = 2` is the one that forces the large window `N ≈ √(2t)`, and it need not be
  searched at all: `C(n,2) = t` happens iff `t` is a triangular number, i.e. iff
  `8t + 1` is a perfect square.  A single square test therefore eliminates the whole
  column `k = 2`, after which every remaining entry satisfies `C(n,3) ≤ t` and the row
  window shrinks from `√(2t)` to `(6t)^{1/3}`.

For `m = 20` the box shrinks from `524248 × 262124` to `9347 × 17`: a saving of more
than nine orders of magnitude, which is what makes the kernel verification of
`m = 11, …, 20` possible.

## Results

* `Singmaster.two_mul_choose_two`, `Singmaster.choose_two_ne_of_not_sq` — the
  triangular obstruction;
* `Singmaster.column_lt_of_choose_eq_centralBinom` — the column collapse;
* `Singmaster.mult_centralBinom_eq_three_cubic` — the resulting criterion;
* `Singmaster.mult_centralBinom_eq_three_of_le_twenty` — `N(C(2m,m)) = 3` for every
  `2 ≤ m ≤ 20`, i.e. up to `C(40,20) = 137846528820`;
* `Singmaster.mult_ne_five_or_seven_of_lt_large` — **unconditionally, no `t` with
  `2 ≤ t < 538257874440 = C(42,21)` occurs exactly five or exactly seven times**,
  extending the previous range `705432` by a factor of more than `700000`.
-/

open Finset

open Singmaster

/-! ## The triangular obstruction: the column `k = 2` -/

/-- `2·C(n+1,2) = (n+1)·n`, proved by induction; the `ℕ`-subtraction-free form of
`Nat.choose_two_right`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * (n + 1).choose 2 = (n + 1) * n := by
  induction n with
  | zero => decide
  | succ r ih =>
    rw [Nat.choose_succ_succ (r + 1) 1, Nat.choose_one_right]
    have hsplit : 2 * ((r + 1) + (r + 1).choose 2) = 2 * (r + 1) + 2 * (r + 1).choose 2 := by
      ring
    rw [hsplit, ih]
    ring


/-! ## The column collapse -/


/-! ## Comparison lemmas for the truncated box -/



/-! ## The criterion -/




/-! ## Executing the criterion for `11 ≤ m ≤ 20`

Each search runs over the rectangle `2m < n < (6t)^{1/3}`, `3 ≤ k ≤ m - 1`; the largest
is `40 < n < 9388`, `3 ≤ k ≤ 19` for `m = 20`.  Every step is a kernel computation:
`decide +kernel` type-checks the Boolean evaluation in the kernel, it is *not*
`native_decide`. -/












/-! ## Unconditional consequences below `C(42,21) = 538257874440` -/




open Singmaster in
theorem solution{n t s : ℕ} (hs1 : s * s < 8 * t + 1)
    (hs2 : 8 * t + 1 < (s + 1) * (s + 1)) : n.choose 2 ≠ t := by
  intro heq
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S * S = 8 * t + 1 := by
    match n with
    | 0 =>
      refine ⟨1, ?_⟩
      rw [← heq]
      decide
    | 1 =>
      refine ⟨1, ?_⟩
      rw [← heq]
      decide
    | (j + 2) =>
      refine ⟨2 * j + 3, ?_⟩
      have hkey : 2 * ((j + 2).choose 2) = (j + 2) * (j + 1) := two_mul_choose_two (j + 1)
      rw [heq] at hkey
      nlinarith [hkey]
  rw [← hS] at hs1 hs2
  have h1 : s < S := by nlinarith
  have h2 : S < s + 1 := by nlinarith
  omega
