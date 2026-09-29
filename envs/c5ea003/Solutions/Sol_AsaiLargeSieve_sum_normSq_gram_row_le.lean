-- Prove2me | solution 1 for AsaiLargeSieve.sum_normSq_gram_row_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:15:58.714188+00:00
-- url     : https://prove2.me/submissions/e45ad835-5af7-47f5-869f-655fcbed9853

-- Sol generated from Novelty/AsaiSchurGap.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSchurGap
import Theorems.Thm_AsaiLargeSieve_cauchy_schwarz_sq
import Theorems.Thm_AsaiLargeSieve_diagonal_le_of_largeSieve
import Theorems.Thm_AsaiLargeSieve_sq_ofReal_norm
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
    ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ^ 2 ≤ C * C := by
  classical
  set a : ℕ → ℂ := fun n => gram S lam m n with ha
  set X : ℝ := ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun n _ => by positivity
  have hGmm : ∑ f ∈ S, ‖lam f m‖ ^ 2 ≤ C := diagonal_le_of_largeSieve S lam N C h hm
  have hGmm0 : (0 : ℝ) ≤ ∑ f ∈ S, ‖lam f m‖ ^ 2 := Finset.sum_nonneg fun f _ => by positivity
  have hC0 : 0 ≤ C := le_trans hGmm0 hGmm
  -- the row `ℓ²`-mass, expressed as a correlation between the family and the row polynomial
  have hid : ((X : ℝ) : ℂ) = ∑ f ∈ S, lam f m * (starRingEnd ℂ) (linForm lam N a f) := by
    have hrhs : ∑ f ∈ S, lam f m * (starRingEnd ℂ) (linForm lam N a f)
        = ∑ n ∈ Finset.range N, (starRingEnd ℂ) (a n) * gram S lam m n := by
      simp only [linForm, map_sum, map_mul, Finset.mul_sum, gram]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Finset.sum_congr rfl fun f _ => by ring
    rw [hrhs, hX]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ha]
    rw [sq_ofReal_norm]
    ring
  have hCS := cauchy_schwarz_sq S (fun f => lam f m) (fun f => linForm lam N a f)
  have hlhs : ‖∑ f ∈ S, lam f m * (starRingEnd ℂ) (linForm lam N a f)‖ ^ 2 = X ^ 2 := by
    rw [← hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
  rw [hlhs] at hCS
  have hLS : ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 ≤ C * X := by
    have := h a
    rwa [← hX] at this
  have hstep : X ^ 2 ≤ C * (C * X) := by
    have h1 : (∑ f ∈ S, ‖lam f m‖ ^ 2) * (∑ f ∈ S, ‖linForm lam N a f‖ ^ 2)
        ≤ C * (C * X) := by
      have hnn : (0 : ℝ) ≤ ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 :=
        Finset.sum_nonneg fun f _ => by positivity
      calc (∑ f ∈ S, ‖lam f m‖ ^ 2) * (∑ f ∈ S, ‖linForm lam N a f‖ ^ 2)
          ≤ C * (∑ f ∈ S, ‖linForm lam N a f‖ ^ 2) := mul_le_mul_of_nonneg_right hGmm hnn
        _ ≤ C * (C * X) := mul_le_mul_of_nonneg_left hLS hC0
    linarith [hCS, h1]
  rcases eq_or_lt_of_le hX0 with hX00 | hXpos
  · rw [← hX00]
    positivity
  · exact le_of_mul_le_mul_right (by nlinarith [hstep] : X * X ≤ (C * C) * X) hXpos
