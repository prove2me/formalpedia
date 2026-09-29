-- Prove2me | Theorems.Thm_AsaiLargeSieve_largeSieve_of_schur
-- name    : AsaiLargeSieve.largeSieve_of_schur
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:00:43.781173+00:00
-- url     : https://prove2.me/theorems/f1277cdd-5b0b-43d0-b499-6117be780d1a
-- title:
--   Schur test for the large sieve.
-- statement:
--   **Schur test for the large sieve.**  If every row of the Gram matrix of the family has
--   `ℓ¹`-norm at most `K` on `[0,N)`, then `K` is an admissible large sieve constant.
--
--   ```lean
--   theorem AsaiLargeSieve.largeSieve_of_schur(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (K : ℝ)
--       (hK : ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ K) :
--       LargeSieve S lam N K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiLargeSieveGram.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiLargeSieveGram.lean#L65

-- Thm stub generated from Novelty/AsaiLargeSieveGram.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
/-
# Gram-matrix criteria for the Asai large sieve: Schur test and exact orthogonality

`Novelty.AsaiLargeSieve` derived the large sieve inequality from a Petersson-type
quasi-orthogonality relation with a *uniform* off-diagonal error.  In the Asai setting this
is the natural output of the Petersson formula: the diagonal `D ≍ k` plus a Kloosterman/Salié
term.  But the uniform bound is wasteful when the off-diagonal correlations decay, so this
file proves two sharper Gram-matrix criteria, both of which have `largeSieve_of_quasiOrthogonal`
as a special case in spirit:

* `AsaiLargeSieve.largeSieve_of_schur` — **Schur test**: if every row of the Gram matrix
  `G m n = ∑_f λ_f(m) conj(λ_f(n))` has `ℓ¹`-norm at most `K`, then `K` is an admissible large
  sieve constant.  The Gram matrix is automatically Hermitian
  (`AsaiLargeSieve.gram_conj_symm`), so no separate column hypothesis is needed — this is the
  structural reason a *one-sided* Schur test suffices here.
* `AsaiLargeSieve.largeSieve_of_diagonal_gram` — **exact orthogonality**: if the correlations
  vanish off the diagonal and the diagonal is bounded by `D`, then `D` is admissible.  This
  is the "no error term at all" case, which the quasi-orthogonality criterion cannot see
  (there the error `e` must dominate the *whole* diagonal deficiency).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the correct general criterion for the Asai large sieve is not
"diagonal + uniform error" but the Schur `ℓ¹`-row bound of the Gram matrix; the Petersson
version should be a corollary, with `K = D + eN` recovered by bounding each row trivially.

Experiment (Experimenter): confirmed by `AsaiLargeSieve.schur_row_bound_of_quasiOrthogonal`,
which shows the Schur constant of a quasi-orthogonal system is at most `D + eN`; so the Schur
test dominates the Petersson test uniformly.  The proof of the Schur test itself is the
AM–GM symmetrisation `|a_m||a_n| ≤ (|a_m|² + |a_n|²)/2` applied inside the Gram expansion,
after which Hermitian symmetry converts the column sums into row sums.

Analysis (Analyst): the failed naive route was to prove the Schur test with both a row and a
column hypothesis; this is redundant because `G` is a Gram matrix, hence Hermitian.  Isolating
`gram_conj_symm` is what makes the one-sided statement provable and is the structural insight
that also gives the two-sided duality in `AsaiLargeSieve`.

Critique (Critic): the exact-orthogonality criterion is not subsumed by the quasi-orthogonal
one (take `D` large and the off-diagonal exactly `0`: the quasi-orthogonal constant is
`D + eN` with `e` forced to be at least the diagonal fluctuation, while here the constant is
exactly the largest diagonal entry), so both are kept.
-/

open Finset Complex

open AsaiLargeSieve

variable {ι : Type*}

theorem AsaiLargeSieve.largeSieve_of_schur(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (K : ℝ)
    (hK : ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ K) :
    LargeSieve S lam N K := by sorry
