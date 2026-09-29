-- Prove2me | solution 1 for AsaiLargeSieve.schur_row_le_sqrt_mul_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:23:31.294606+00:00
-- url     : https://prove2.me/submissions/63272aea-c612-4f91-9fb3-74bfa2c4aa01

-- Sol generated from Novelty/AsaiSchurGap.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSchurGap
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


/-- The `ℓ²`-mass of the rank-one system on `[0, M+1)`. -/
theorem sum_normSq_rankOne (eps : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), ‖rankOneFamily eps () n‖ ^ 2 = 1 + M * eps ^ 2 := by
  rw [Finset.sum_range_succ']
  simp [rankOneFamily, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- The `ℓ¹`-mass of the rank-one system on `[0, M+1)`, for `ε ≥ 0`. -/
theorem sum_norm_rankOne {eps : ℝ} (heps : 0 ≤ eps) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), ‖rankOneFamily eps () n‖ = 1 + M * eps := by
  rw [Finset.sum_range_succ']
  simp [rankOneFamily, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg heps]
  ring


/-- **The Schur row of the rank-one family** at `m = 0` is `‖v‖_∞ · ‖v‖₁ = 1 + M ε`. -/
theorem schur_row_rankOne {eps : ℝ} (heps : 0 ≤ eps) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1),
        ‖gram (Finset.univ : Finset Unit) (rankOneFamily eps) 0 n‖ = 1 + M * eps := by
  have hpt : ∀ n, gram (Finset.univ : Finset Unit) (rankOneFamily eps) 0 n
      = (starRingEnd ℂ) (rankOneFamily eps () n) := by
    intro n
    rw [gram]
    simp [rankOneFamily]
  have : ∀ n, ‖gram (Finset.univ : Finset Unit) (rankOneFamily eps) 0 n‖
      = ‖rankOneFamily eps () n‖ := by
    intro n; rw [hpt n, RCLike.norm_conj]
  rw [Finset.sum_congr rfl fun n _ => this n]
  exact sum_norm_rankOne heps M




/-! ## The corrected comparison, in general

The counterexample above rules out `K_Schur ≤ K · C_opt` for an absolute constant `K`.  The
right statement is `K_Schur ≤ √N · C_opt`, and it holds for *every* family: the row `m` of the
Gram matrix has `ℓ²`-norm at most `C` (this is `sum_normSq_gram_row_le`, a self-testing
Cauchy–Schwarz argument — one applies the large sieve inequality to the row itself), and
`ℓ¹ ≤ √N · ℓ²`.  A rank-one family shows the exponent `1/2` is optimal up to a factor `2`. -/

variable {ι : Type*}





open AsaiLargeSieve in
theorem solution{eps : ℝ} (heps : 0 ≤ eps) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1),
        ‖gram (Finset.univ : Finset Unit) (rankOneFamily eps) 0 n‖
      ≤ Real.sqrt ((M : ℝ) + 1) * ∑ n ∈ Finset.range (M + 1),
          ‖rankOneFamily eps () n‖ ^ 2 := by
  rw [schur_row_rankOne heps M, sum_normSq_rankOne eps M]
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hs0 : 0 ≤ Real.sqrt ((M : ℝ) + 1) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt ((M : ℝ) + 1) ^ 2 = (M : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt ((M : ℝ) + 1) := by nlinarith [hs0, hs2]
  have hB1 : (1 : ℝ) ≤ 1 + (M : ℝ) * eps ^ 2 := by nlinarith [sq_nonneg eps]
  have hA0 : (0 : ℝ) ≤ 1 + (M : ℝ) * eps := by positivity
  -- `‖v‖₁² ≤ N · ‖v‖₂²` is Cauchy–Schwarz, here an instance of `M (ε - 1)² ≥ 0`
  have hl1 : (1 + (M : ℝ) * eps) ^ 2 ≤ ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2) := by
    nlinarith [mul_nonneg hM (sq_nonneg (eps - 1))]
  have hB2 : (1 + (M : ℝ) * eps ^ 2) ≤ (1 + (M : ℝ) * eps ^ 2) ^ 2 := by nlinarith [hB1]
  have hstep : ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2)
      ≤ ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hB2 (by linarith)
  have hsq : (1 + (M : ℝ) * eps) ^ 2
      ≤ (Real.sqrt ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2)) ^ 2 := by
    have hexp : (Real.sqrt ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2)) ^ 2
        = ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2) ^ 2 := by
      rw [mul_pow, hs2]
    rw [hexp]
    linarith
  have hrhs0 : (0 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) * (1 + (M : ℝ) * eps ^ 2) := by
    have : (0 : ℝ) ≤ 1 + (M : ℝ) * eps ^ 2 := by linarith
    exact mul_nonneg hs0 this
  nlinarith [hsq, hrhs0, hA0]
