-- Prove2me | solution 1 for AsaiLargeSieve.abs_sub_diagonal_le_of_quasiOrthogonal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:00:37.544114+00:00
-- url     : https://prove2.me/submissions/4b779c0a-049f-48c3-a546-a0f2894698d8

-- Sol generated from Novelty/AsaiLargeSieve.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Theorems.Thm_AsaiLargeSieve_sq_ofReal_norm
import Theorems.Thm_AsaiLargeSieve_sq_sum_norm_le
import Theorems.Thm_AsaiLargeSieve_sum_normSq_linForm_eq
/-
# A formal large-sieve framework for Asai lifts

This file formalises, in a self-contained and quantitative way, the *analytic skeleton*
behind the paper **"On the Second Moment of `L(1/2, As(f) × φ)`"**: for `F = Q(√D)` a real
quadratic field and `f` running over a Hecke orthonormal basis of Hilbert modular cusp forms
of parallel weight `(k,k)` over `F`, one proves a **large sieve inequality** for the Hecke
eigenvalues of the Asai lifts `As(f)`, and then feeds an approximate functional equation into
it to bound the second moment of the central values `L(1/2, As(f) × φ)`.

What is formalised here is exactly the part of that argument that is *pure inequality
theory* — and it is formalised for an arbitrary finite family of "eigenvalue systems"
`lam : ι → ℕ → ℂ`, so that the Asai situation is one instance:

* `AsaiLargeSieve.LargeSieve S lam N C` — the large sieve inequality
  `∑_{f ∈ S} |∑_{n < N} a n · lam f n|² ≤ C · ∑_{n<N} |a n|²`.
* `AsaiLargeSieve.QuasiOrthogonal S lam N Δ ε` — a Petersson-type quasi-orthogonality
  relation `∑_{f ∈ S} lam f m · conj (lam f n) = Δ·δ_{m,n} + O(ε)`.

Main results:

* `AsaiLargeSieve.sum_normSq_linForm_eq` — the exact Gram expansion of the left-hand side of
  the large sieve into the correlation sums `∑_f lam f m · conj (lam f n)`.
* `AsaiLargeSieve.abs_sub_diagonal_le_of_quasiOrthogonal` — the two-sided estimate from which
  both the large sieve inequality and its matching lower bound follow.
* `AsaiLargeSieve.lowerBound_of_quasiOrthogonal` and
  `AsaiLargeSieve.secondMoment_order_of_quasiOrthogonal` — in the regime `2eN ≤ D` the second
  moment of a one-block Dirichlet polynomial has the *exact* order `D`, between `D/2` and
  `3D/2` times the coefficient mass; so the large sieve constant is of the correct order and
  not merely an upper bound.
* `AsaiLargeSieve.largeSieve_of_quasiOrthogonal` — **Petersson ⇒ large sieve**:
  quasi-orthogonality with diagonal `Δ` and off-diagonal error `ε` yields the large sieve
  constant `Δ + εN`.  This is the abstract form of the paper's Theorem on `As(f)`, where
  `Δ ≍ k` and `εN` is the Kloosterman/Salié contribution.
* `AsaiLargeSieve.dualLargeSieve_of_largeSieve` (and its converse
  `AsaiLargeSieve.largeSieve_of_dualLargeSieve`) — **duality**: the large sieve constant is
  the operator norm of the coefficient matrix, so it is the same for the matrix and its
  adjoint.  Proved by the self-testing trick, with no matrix theory.
* `AsaiLargeSieve.largeSieve_twist` — twisting the eigenvalue system by the (bounded) Hecke
  eigenvalues of a fixed cusp form `φ` costs only `ν²`; this is what converts a large sieve
  for `As(f)` into one for the Rankin–Selberg coefficients of `As(f) × φ`.
* `AsaiLargeSieve.diagonal_le_of_largeSieve`, `AsaiLargeSieve.trivialConstant_ge`,
  `AsaiLargeSieve.largeSieve_gain` — sharpness: any admissible constant dominates each
  diagonal term, the trivial (Cauchy–Schwarz) constant is `≥ N(Δ - ε)`, and hence the
  Petersson constant `Δ + εN` genuinely saves a factor `≍ N` whenever `εN ≤ Δ`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the whole large sieve half of the paper is a *finite-dimensional
operator norm statement*; the arithmetic (Asai lifts, real quadratic field, Petersson formula
with Salié sums) only enters through two scalars, the diagonal mass `Δ` and the off-diagonal
uniform error `ε`.  Bold form: the implication `Petersson ⇒ large sieve ⇒ second moment`
should be provable with *no* modular forms at all, and the resulting constant `Δ + εN` should
be sharp up to the factor `N` measured by `largeSieve_gain`.

Experiment (Experimenter): the Gram expansion `sum_normSq_linForm_eq` is an exact identity in
`ℂ`; separating the diagonal `Δ·δ` from the error and estimating `|∑_{m,n} a_m conj(a_n) E|
≤ ε (∑|a_n|)² ≤ εN ∑|a_n|²` (Cauchy–Schwarz against the constant `1`) gives the constant
`Δ + εN` unconditionally, with no positivity assumption on `Δ` or `ε`.  Duality was the one
place where the naive route (adjoint operators) is heavy; the self-testing choice
`a_n := ∑_f c_f conj(lam f n)` makes it a three-line Cauchy–Schwarz.

Analysis (Analyst): the failure mode of a naive attempt is the temptation to prove
`‖M‖ = ‖Mᵀ‖` through the spectral theorem.  The correct structural statement is that the
large sieve constant is a *quadratic form bound tested on the extremal vector*; both
directions of duality then have literally the same proof.  A second structural point: the
`εN` term is unavoidable, since `largeSieve_gain` shows the trivial constant is `≥ N(Δ-ε)`;
so `Δ + εN` is nontrivial precisely in the regime `ε ≤ Δ/N`, i.e. square-root cancellation
in the Kloosterman/Salié term — exactly the paper's threshold.

Critique (Critic): no statement here is vacuous — `diagonal_le_of_largeSieve` shows every
`LargeSieve` hypothesis has real content (it forces `C ≥ ∑_f |lam f n|²`), and the twisting
lemma is stated with an explicit bound `ν` rather than an unquantified `O(1)`.  The
hypotheses that are *not* needed (positivity of `Δ`, `ε`, or `C`) were deliberately dropped.
-/

open Finset Complex

open AsaiLargeSieve

variable {ι : Type*}

/-! ## Definitions -/





/-! ## Elementary tools -/



/-- The norm of the complexification of a real difference. -/
theorem norm_ofReal_sub (x y : ℝ) : ‖((x : ℂ) - (y : ℂ))‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]



/-! ## The Gram expansion -/


/-- The diagonal part of the Gram expansion. -/
theorem diagonal_sum_eq (N : ℕ) (a : ℕ → ℂ) (D : ℝ) :
    ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      a m * (starRingEnd ℂ) (a n) * (if m = n then (D : ℂ) else 0)
      = (D : ℂ) * ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_eq_single m]
  · rw [← sq_ofReal_norm]
    simp
    ring
  · intro n _ hne
    simp [Ne.symm hne]
  · intro h; exact absurd hm h

/-! ## Petersson ⇒ two-sided control of the quadratic form -/





/-! ## Duality -/



/-! ## Twisting by a fixed form -/


/-! ## Sharpness -/






open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ)
    (D e : ℝ) (h : QuasiOrthogonal S lam N D e) (a : ℕ → ℂ) :
    |(∑ f ∈ S, ‖linForm lam N a f‖ ^ 2) - D * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2|
      ≤ e * N * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp [linForm]
  have he0 : 0 ≤ e :=
    le_trans (norm_nonneg _)
      (h 0 (Finset.mem_range.mpr hNpos) 0 (Finset.mem_range.mpr hNpos))
  set R : ℝ := ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 with hR
  set A : ℝ := ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 with hA
  set E : ℕ → ℕ → ℂ := fun m n =>
    (∑ f ∈ S, lam f m * (starRingEnd ℂ) (lam f n)) - (if m = n then (D : ℂ) else 0) with hE
  have key : ((R - D * A : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, a m * (starRingEnd ℂ) (a n) * E m n := by
    have h1 := sum_normSq_linForm_eq S lam N a
    have h2 := diagonal_sum_eq N a D
    push_cast
    rw [← hR] at h1
    rw [← hA] at h2
    rw [h1, ← h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hE]; ring
  have hbound : |R - D * A| ≤ e * ((∑ n ∈ Finset.range N, ‖a n‖) ^ 2) := by
    have hnorm : ‖((R : ℂ) - (D * A : ℝ))‖ = |R - D * A| := norm_ofReal_sub R (D * A)
    rw [show |R - D * A| = ‖((R - D * A : ℝ) : ℂ)‖ by
        rw [show ((R - D * A : ℝ) : ℂ) = (R : ℂ) - ((D * A : ℝ) : ℂ) by push_cast; ring, hnorm],
      key]
    have step1 : ‖∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        a m * (starRingEnd ℂ) (a n) * E m n‖
        ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖a m‖ * ‖a n‖ * e := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hEmn : ‖E m n‖ ≤ e := h m hm n hn
      have : ‖a m * (starRingEnd ℂ) (a n) * E m n‖ = ‖a m‖ * ‖a n‖ * ‖E m n‖ := by
        simp
      rw [this]
      have hpos : (0 : ℝ) ≤ ‖a m‖ * ‖a n‖ := by positivity
      exact mul_le_mul_of_nonneg_left hEmn hpos
    refine step1.trans_eq ?_
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hcs : (∑ n ∈ Finset.range N, ‖a n‖) ^ 2 ≤ (N : ℝ) * A := sq_sum_norm_le N a
  have he : e * ((∑ n ∈ Finset.range N, ‖a n‖) ^ 2) ≤ e * ((N : ℝ) * A) :=
    mul_le_mul_of_nonneg_left hcs he0
  calc |R - D * A| ≤ e * ((∑ n ∈ Finset.range N, ‖a n‖) ^ 2) := hbound
    _ ≤ e * ((N : ℝ) * A) := he
    _ = e * N * A := by ring
