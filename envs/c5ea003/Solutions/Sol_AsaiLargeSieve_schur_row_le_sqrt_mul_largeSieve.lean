-- Prove2me | solution 1 for AsaiLargeSieve.schur_row_le_sqrt_mul_largeSieve
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:23:30.433387+00:00
-- url     : https://prove2.me/submissions/e485d15c-b676-4add-921f-751464490b89

-- Sol generated from Novelty/AsaiSchurGap.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSchurGap
import Theorems.Thm_AsaiLargeSieve_diagonal_le_of_largeSieve
import Theorems.Thm_AsaiLargeSieve_sq_sum_norm_le
import Theorems.Thm_AsaiLargeSieve_sum_normSq_gram_row_le
/-
# The Schur constant is *not* comparable to the large sieve constant

This file continues the formalisation of the analytic skeleton of the paper
**"On the Second Moment of `L(1/2, As(f) × φ)`"** (`Novelty.AsaiLargeSieve`,
`Novelty.AsaiLargeSieveGram`, `Novelty.AsaiLargeSieveSharp`, …).  It **refutes** conjecture
**C1** of `FUTURE_DIRECTIONS.md` in its general form, and thereby delimits exactly the range
of validity of the positive result `AsaiLargeSieve.schur_row_le_two_mul_largeSieve_of_dominant`.

## The conjecture and its fate

C1 asserted that for every family the Schur constant
`K_Schur = max_{m<N} ∑_{n<N} ‖gram S lam m n‖` and the optimal large sieve constant `C_opt`
satisfy `C_opt ≤ K_Schur ≤ 2 · C_opt`.  The first inequality is
`AsaiLargeSieveGram.largeSieve_of_schur`.  The second is proved in
`AsaiLargeSieveSharp.schur_row_le_two_mul_largeSieve_of_dominant` under diagonal dominance —
the regime in which the paper works — and it is proved here that **it is false in general**,
and not merely with the constant `2`: no constant whatsoever works.

The counterexample is a rank-one family (`rankOneFamily`): a single form with eigenvalue
system `v = (1, ε, ε, …, ε)`, `M` copies of `ε`.  Its Gram matrix is `v vᵀ`, which is
Hermitian positive semidefinite, so no positivity hypothesis is being violated.  For this
family

* the trivial (and here optimal) large sieve constant is `‖v‖₂² = 1 + M ε²`
  (`largeSieve_rankOne`), while
* the Schur row at `m = 0` is `‖v‖_∞ ‖v‖₁ = 1 + M ε` (`schur_row_rankOne`).

Choosing `ε = 1/m` and `M = m³` gives `C = 1 + m` and `K_Schur ≥ 1 + m²`, a ratio `≍ m` which
is unbounded (`schur_row_gap_unbounded`); already `m = 4` (so `N = 65`, `C = 5`,
`K_Schur = 17`) breaks the conjectured constant `2`
(`schur_row_not_le_two_mul_largeSieve`).

## What survives, and the corrected statement (conjecture C8, settled here)

The positive result under diagonal dominance
(`AsaiLargeSieveSharp.schur_row_le_two_mul_largeSieve_of_dominant`) is untouched: the
counterexample is very far from diagonally dominant.  The correct comparison in general turns
out to be `K_Schur ≤ √N · C_opt`, and it is proved here for every family:

* `sum_normSq_gram_row_le` — the `ℓ²`-norm of a Gram row is at most `C`.  The proof tests the
  large sieve inequality against the row itself and uses Cauchy–Schwarz over the family.
* `schur_row_le_sqrt_mul_largeSieve` — hence `K_Schur ≤ √N · C`, improving the earlier
  unconditional `K_Schur ≤ N · C` (`AsaiLargeSieveSharp.schur_row_le_of_largeSieve`) by a full
  square root.
* `schur_row_sqrt_attained` — the exponent `1/2` is optimal up to a factor `2`: the rank-one
  family with `ε = 1/m` and `m²` copies of `ε` has `N = m² + 1`, admits `C = 2` and has Schur
  row `1 + m ≥ √N`.
* `schur_row_le_sqrt_mul_rankOne` — the rank-one case, proved directly.
-/

open Finset Complex

open AsaiLargeSieve









/-! ## The corrected comparison, in general

The counterexample above rules out `K_Schur ≤ K · C_opt` for an absolute constant `K`.  The
right statement is `K_Schur ≤ √N · C_opt`, and it holds for *every* family: the row `m` of the
Gram matrix has `ℓ²`-norm at most `C` (this is `sum_normSq_gram_row_le`, a self-testing
Cauchy–Schwarz argument — one applies the large sieve inequality to the row itself), and
`ℓ¹ ≤ √N · ℓ²`.  A rank-one family shows the exponent `1/2` is optimal up to a factor `2`. -/

variable {ι : Type*}





open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
    (h : LargeSieve S lam N C) {m : ℕ} (hm : m < N) :
    ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ Real.sqrt (N : ℝ) * C := by
  have hGmm : ∑ f ∈ S, ‖lam f m‖ ^ 2 ≤ C := diagonal_le_of_largeSieve S lam N C h hm
  have hC0 : 0 ≤ C := le_trans (Finset.sum_nonneg fun f _ => by positivity) hGmm
  have hrow := sum_normSq_gram_row_le S lam N C h hm
  have hl1 := sq_sum_norm_le N (fun n => gram S lam m n)
  have hsN : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsN0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsum0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖gram S lam m n‖ :=
    Finset.sum_nonneg fun n _ => norm_nonneg _
  have hsq : (∑ n ∈ Finset.range N, ‖gram S lam m n‖) ^ 2 ≤ (Real.sqrt (N : ℝ) * C) ^ 2 := by
    have hNC : (N : ℝ) * (∑ n ∈ Finset.range N, ‖gram S lam m n‖ ^ 2) ≤ (N : ℝ) * (C * C) :=
      mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg N)
    have hexp : (Real.sqrt (N : ℝ) * C) ^ 2 = (N : ℝ) * (C * C) := by
      rw [mul_pow, hsN]; ring
    rw [hexp]
    linarith [hl1, hNC]
  nlinarith [hsq, hsum0, mul_nonneg hsN0 hC0]
