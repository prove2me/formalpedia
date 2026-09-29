-- Prove2me | Theorems.Thm_AsaiLargeSieve_schur_row_gap_unbounded
-- name    : AsaiLargeSieve.schur_row_gap_unbounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:01:32.629192+00:00
-- url     : https://prove2.me/theorems/d4f52905-9403-46d3-aa0f-0930dbc66693
-- title:
--   Conjecture C1 is false, with room to spare.
-- statement:
--   **Conjecture C1 is false, with room to spare.**  For every constant `K` there is a family
--   (with Hermitian positive semidefinite Gram matrix) and an admissible large sieve constant `C`
--   for it whose Schur row at `m = 0` exceeds `K · C`.  Hence no inequality of the form
--   `K_Schur ≤ K · C_opt` can hold with an absolute constant `K`.
--
--   ```lean
--   theorem AsaiLargeSieve.schur_row_gap_unbounded(K : ℝ) :
--       ∃ (N : ℕ) (lam : Unit → ℕ → ℂ) (C : ℝ),
--         LargeSieve (Finset.univ : Finset Unit) lam N C ∧ 0 < C ∧
--           K * C < ∑ n ∈ Finset.range N, ‖gram (Finset.univ : Finset Unit) lam 0 n‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiSchurGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiSchurGap.lean#L103

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

theorem AsaiLargeSieve.schur_row_gap_unbounded(K : ℝ) :
    ∃ (N : ℕ) (lam : Unit → ℕ → ℂ) (C : ℝ),
      LargeSieve (Finset.univ : Finset Unit) lam N C ∧ 0 < C ∧
        K * C < ∑ n ∈ Finset.range N, ‖gram (Finset.univ : Finset Unit) lam 0 n‖ := by sorry
