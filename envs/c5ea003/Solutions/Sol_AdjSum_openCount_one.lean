-- Prove2me | solution 1 for AdjSum.openCount_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:39:13.277113+00:00
-- url     : https://prove2.me/submissions/0476ccc1-1e9a-47b1-9cc9-82504b621d80

-- Sol generated from Applications/AdjacentSumPolytopes/Growth.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence
import Theorems.Thm_AdjSum_card_openSet

/-!
# Exponential growth of the adjacent-sum counts, and the two-state Fibonacci model

The recurrences of `Applications.AdjacentSumPolytopes.Recurrence` say *nothing* about
the size of the counts.  Here we bracket the growth of both parity classes by explicit
exponentials, using only entrywise nonnegativity of the transfer matrix — no
Perron–Frobenius theory is required:

`(⌊s/2⌋+1)^(d+1) ≤ #(cyclic points of length d+1) ≤ (s+1)^(d+1)`,
`(⌊s/2⌋+1)^(d+2) ≤ #(open points of length d+2)  ≤ (s+1)^(d+2)`.

The lower bound comes from the *core block* of states `a` with `2a ≤ s`: any two such
states are compatible, so the all-ones matrix on that block is entrywise below the
transfer matrix.  The upper bound compares with the all-ones matrix on all states.

Consequently the dominant real pole `1/λ_s` of the shared denominator satisfies
`1/(s+1) ≤ 1/λ_s ≤ 1/(⌊s/2⌋+1)`; in particular the counts grow strictly exponentially
as soon as `s ≥ 2` (`cycCount_two_pow_le`).

We also identify the two-state (`s = 1`) case completely: the open counts are Fibonacci
numbers and the cyclic counts are Lucas numbers.

-- !-- Lab Notes -- !--
* **Hypothesis.** The all-ones block on `{a : 2a ≤ s}` should already give the right
  order of growth; the true growth constant `λ_s` should sit strictly between
  `⌊s/2⌋+1` and `s+1` for `s ≥ 2`.
* **Experiment.** Cyclic counts for `s = 2` are `2, 6, 11, 26, 57, 129, 289, 650`;
  successive ratios `2.36, 2.26, 2.25, ...` approach the dominant root of
  `x³ − 2x² − x + 1`, which lies strictly between `⌊2/2⌋+1 = 2` and `3`.  For `s = 3`:
  `2, 10, 23, 70, 197, 571, 1640` with ratios approaching `≈ 2.87 ∈ (2, 4)`.
* **Analysis.** The block bound is tight in order of magnitude but not in constant;
  the ratio `λ_s/(⌊s/2⌋+1)` appears to converge, which we record as a conjecture.
* **Critique.** The bounds hold for every `s` and every `d` with no hypotheses, and are
  *strict* exponentials (base `≥ 2`) exactly when `s ≥ 2`; for `s = 0` both bounds
  collapse to `1`, correctly, since the only lattice point is the origin.
-/

open AdjSum

open Finset Matrix

/-! ## Monotonicity of powers of nonnegative matrices -/



/-! ## All-ones blocks -/






/-! ## The core block of mutually compatible states -/





/-! ## Exponential bounds -/






/-! ## The two-state model: Fibonacci and Lucas numbers -/

theorem adjMat_one_eq : adjMat 1 = !![1, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [adjMat]

/-- The powers of the two-state transfer matrix are the Fibonacci matrices. -/
theorem adjMat_one_pow (n : ℕ) :
    adjMat 1 ^ (n + 1) = !![Nat.fib (n + 2), Nat.fib (n + 1); Nat.fib (n + 1), Nat.fib n] := by
  induction n with
  | zero => rw [pow_one, adjMat_one_eq]; norm_num
  | succ n ih =>
      rw [pow_succ, ih, adjMat_one_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two] <;> ring




open AdjSum in
theorem solution(d : ℕ) : openCount 1 d = Nat.fib (d + 3) := by
  rw [openCount, card_openSet]
  match d with
  | 0 =>
      simp only [pow_zero, Matrix.one_apply]
      decide
  | (n + 1) =>
      rw [adjMat_one_pow n]
      have e1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        rw [show n + 4 = (n + 2) + 2 from by omega]; exact Nat.fib_add_two
      have e2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        rw [show n + 3 = (n + 1) + 2 from by omega]; exact Nat.fib_add_two
      have e3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      rw [show n + 1 + 3 = n + 4 from by omega]
      simp [Fin.sum_univ_two]
      omega
