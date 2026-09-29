-- Prove2me | solution 1 for AsaiLargeSieve.largeSieve_of_schur
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:06:42.073627+00:00
-- url     : https://prove2.me/submissions/bf6ad88b-6fcf-4960-9fae-34b83b87aa77

-- Sol generated from Novelty/AsaiLargeSieveGram.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
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


/-- The Gram matrix is Hermitian. -/
theorem gram_conj_symm (S : Finset ι) (lam : ι → ℕ → ℂ) (m n : ℕ) :
    gram S lam n m = (starRingEnd ℂ) (gram S lam m n) := by
  rw [gram, gram, map_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [map_mul, Complex.conj_conj]; ring

/-- Consequently the row and column `ℓ¹`-norms agree entrywise. -/
theorem norm_gram_symm (S : Finset ι) (lam : ι → ℕ → ℂ) (m n : ℕ) :
    ‖gram S lam n m‖ = ‖gram S lam m n‖ := by
  rw [gram_conj_symm, RCLike.norm_conj]





open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (K : ℝ)
    (hK : ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ K) :
    LargeSieve S lam N K := by
  intro a
  set R : ℝ := ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun f _ => by positivity
  have hexp : ((R : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          a m * (starRingEnd ℂ) (a n) * gram S lam m n := by
    rw [hR]; exact sum_normSq_linForm_eq S lam N a
  have h1 : R ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      ‖a m‖ * ‖a n‖ * ‖gram S lam m n‖ := by
    have hnorm : R = ‖((R : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
    rw [hnorm, hexp]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    simp
  have h2 : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N,
      ‖a m‖ * ‖a n‖ * ‖gram S lam m n‖
        ≤ ((‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2) * ‖gram S lam m n‖ := by
    intro m _ n _
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)]
  have h3 : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      ((‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2) * ‖gram S lam m n‖
      = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a m‖ ^ 2 * ‖gram S lam m n‖) / 2
        + (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * ‖gram S lam m n‖) / 2 := by
    simp_rw [add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div]
  -- row sums
  have hrow : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a m‖ ^ 2 * ‖gram S lam m n‖
      ≤ K * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
    have : ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a m‖ ^ 2 * ‖gram S lam m n‖
        ≤ ‖a m‖ ^ 2 * K := by
      intro m hm
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hK m hm) (by positivity)
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.sum_mul, mul_comm]
  -- column sums, converted to row sums by Hermitian symmetry
  have hcol : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * ‖gram S lam m n‖
      ≤ K * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
    have hswap : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * ‖gram S lam m n‖
        = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖a n‖ ^ 2 * ‖gram S lam n m‖ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      rw [norm_gram_symm]
    rw [hswap]
    have : ∀ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖a n‖ ^ 2 * ‖gram S lam n m‖
        ≤ ‖a n‖ ^ 2 * K := by
      intro n hn
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hK n hn) (by positivity)
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.sum_mul, mul_comm]
  have hmid : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      ‖a m‖ * ‖a n‖ * ‖gram S lam m n‖ ≤ K * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
    refine (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => h2 m hm n hn).trans ?_
    rw [h3]
    linarith
  exact h1.trans hmid
