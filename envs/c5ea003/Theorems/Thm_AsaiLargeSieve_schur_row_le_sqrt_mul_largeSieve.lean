-- Prove2me | Theorems.Thm_AsaiLargeSieve_schur_row_le_sqrt_mul_largeSieve
-- name    : AsaiLargeSieve.schur_row_le_sqrt_mul_largeSieve
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:02:11.667602+00:00
-- url     : https://prove2.me/theorems/a54e9622-330d-4655-b064-f3a0096daf4f
-- title:
--   Conjecture C8, upper half, proved in general.
-- statement:
--   **Conjecture C8, upper half, proved in general.**  Every admissible large sieve constant
--   `C` bounds the Schur rows by `√N · C`; this is the correct replacement for the refuted
--   constant-factor comparison, and it improves the earlier unconditional bound `N · C` of
--   `AsaiLargeSieveSharp.schur_row_le_of_largeSieve`.
--
--   ```lean
--   theorem AsaiLargeSieve.schur_row_le_sqrt_mul_largeSieve(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
--       (h : LargeSieve S lam N C) {m : ℕ} (hm : m < N) :
--       ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ Real.sqrt (N : ℝ) * C := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiSchurGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiSchurGap.lean#L239

-- Thm stub generated from Novelty/AsaiSchurGap.lean
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









/-! ## The corrected comparison, in general

The counterexample above rules out `K_Schur ≤ K · C_opt` for an absolute constant `K`.  The
right statement is `K_Schur ≤ √N · C_opt`, and it holds for *every* family: the row `m` of the
Gram matrix has `ℓ²`-norm at most `C` (this is `sum_normSq_gram_row_le`, a self-testing
Cauchy–Schwarz argument — one applies the large sieve inequality to the row itself), and
`ℓ¹ ≤ √N · ℓ²`.  A rank-one family shows the exponent `1/2` is optimal up to a factor `2`. -/

variable {ι : Type*}

theorem AsaiLargeSieve.schur_row_le_sqrt_mul_largeSieve(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
    (h : LargeSieve S lam N C) {m : ℕ} (hm : m < N) :
    ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ Real.sqrt (N : ℝ) * C := by sorry
