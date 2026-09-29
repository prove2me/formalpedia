-- Prove2me | solution 1 for AsaiLargeSieve.largeSieve_of_diagonal_gram
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:06:40.777507+00:00
-- url     : https://prove2.me/submissions/38c30c95-5637-4b50-9989-11c9a9103279

-- Sol generated from Novelty/AsaiLargeSieveGram.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Theorems.Thm_AsaiLargeSieve_sq_ofReal_norm
import Theorems.Thm_AsaiLargeSieve_sum_normSq_linForm_eq
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








open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (D : ℝ)
    (hoff : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n → gram S lam m n = 0)
    (hdiag : ∀ n ∈ Finset.range N, ∑ f ∈ S, ‖lam f n‖ ^ 2 ≤ D) :
    LargeSieve S lam N D := by
  intro a
  have hexp : ((∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          a m * (starRingEnd ℂ) (a n) * gram S lam m n := sum_normSq_linForm_eq S lam N a
  have hcollapse : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      a m * (starRingEnd ℂ) (a n) * gram S lam m n
      = ∑ m ∈ Finset.range N, ((‖a m‖ : ℂ)) ^ 2 * gram S lam m m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_eq_single m]
    · rw [sq_ofReal_norm]
    · intro n hn hne
      rw [hoff m hm n hn (Ne.symm hne), mul_zero]
    · intro hmem; exact absurd hm hmem
  have hdiagreal : ∀ m, gram S lam m m = ((∑ f ∈ S, ‖lam f m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    rw [gram]
    push_cast
    exact (Finset.sum_congr rfl fun f _ => by rw [sq_ofReal_norm]).symm
  have hreal : ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2
      = ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 * ∑ f ∈ S, ‖lam f m‖ ^ 2 := by
    have hc : ((∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 : ℝ) : ℂ)
        = ((∑ m ∈ Finset.range N, ‖a m‖ ^ 2 * ∑ f ∈ S, ‖lam f m‖ ^ 2 : ℝ) : ℂ) := by
      rw [hexp, hcollapse]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hdiagreal m]
      push_cast
      ring
    exact_mod_cast hc
  rw [hreal, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hdiag m hm) (by positivity)
