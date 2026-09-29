-- Prove2me | solution 1 for AsaiLargeSieve.schur_row_bound_of_quasiOrthogonal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:15:50.044273+00:00
-- url     : https://prove2.me/submissions/3e3133b6-b7b0-4d7e-991a-50e6b7dbc7fc

-- Sol generated from Novelty/AsaiLargeSieveGram.lean
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








open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (D e : ℝ)
    (hD : 0 ≤ D) (h : QuasiOrthogonal S lam N D e) :
    ∀ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ D + e * N := by
  intro m hm
  have hpt : ∀ n ∈ Finset.range N,
      ‖gram S lam m n‖ ≤ (if m = n then D else 0) + e := by
    intro n hn
    have hq := h m hm n hn
    have : ‖gram S lam m n‖ - ‖(if m = n then (D : ℂ) else 0)‖
        ≤ ‖gram S lam m n - (if m = n then (D : ℂ) else 0)‖ := norm_sub_norm_le _ _
    have hdif : ‖(if m = n then (D : ℂ) else 0)‖ = (if m = n then D else 0) := by
      by_cases hmn : m = n <;> simp [hmn, abs_of_nonneg hD]
    rw [hdif] at this
    have hq' : ‖gram S lam m n - (if m = n then (D : ℂ) else 0)‖ ≤ e := by
      rw [gram]; exact hq
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hone : ∑ n ∈ Finset.range N, (if m = n then D else 0) = D := by
    rw [Finset.sum_ite_eq (Finset.range N) m (fun _ => D), if_pos hm]
  rw [hone, mul_comm]
