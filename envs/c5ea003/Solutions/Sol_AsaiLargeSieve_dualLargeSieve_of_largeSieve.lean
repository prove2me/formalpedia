-- Prove2me | solution 1 for AsaiLargeSieve.dualLargeSieve_of_largeSieve
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:03:42.021385+00:00
-- url     : https://prove2.me/submissions/ed33e8c8-9d21-4b2a-af0e-cd53ae5874e6

-- Sol generated from Novelty/AsaiLargeSieve.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Theorems.Thm_AsaiLargeSieve_cauchy_schwarz_sq
import Theorems.Thm_AsaiLargeSieve_sq_ofReal_norm
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






/-! ## The Gram expansion -/



/-! ## Petersson ⇒ two-sided control of the quadratic form -/





/-! ## Duality -/



/-! ## Twisting by a fixed form -/


/-! ## Sharpness -/






open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (h : LargeSieve S lam N C) : DualLargeSieve S lam N C := by
  intro c
  set Sq : ℝ := ∑ n ∈ Finset.range N, ‖∑ f ∈ S, c f * (starRingEnd ℂ) (lam f n)‖ ^ 2 with hSq
  set a : ℕ → ℂ := fun n => ∑ f ∈ S, c f * (starRingEnd ℂ) (lam f n) with ha
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun n _ => by positivity
  have hpair : ((Sq : ℝ) : ℂ) = ∑ f ∈ S, (starRingEnd ℂ) (c f) * linForm lam N a f := by
    have : ((Sq : ℝ) : ℂ) = ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n) := by
      rw [hSq]
      push_cast
      exact Finset.sum_congr rfl fun n _ => by rw [← sq_ofReal_norm]
    rw [this]
    calc ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n)
        = ∑ n ∈ Finset.range N, ∑ f ∈ S, a n * ((starRingEnd ℂ) (c f) * lam f n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ha]
          simp only [map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
      _ = ∑ f ∈ S, (starRingEnd ℂ) (c f) * linForm lam N a f := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [linForm, Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
  have hcs : Sq ^ 2 ≤ (∑ f ∈ S, ‖c f‖ ^ 2) * (∑ f ∈ S, ‖linForm lam N a f‖ ^ 2) := by
    have := cauchy_schwarz_sq S (fun f => (starRingEnd ℂ) (c f))
      (fun f => (starRingEnd ℂ) (linForm lam N a f))
    simp only [Complex.conj_conj] at this
    have hrw : ‖∑ f ∈ S, (starRingEnd ℂ) (c f) * linForm lam N a f‖ = |Sq| := by
      rw [← hpair]; simp
    rw [hrw, abs_of_nonneg hSq0] at this
    simpa using this
  have hLS : ∑ f ∈ S, ‖linForm lam N a f‖ ^ 2 ≤ C * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := h a
  have hAeq : ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 = Sq := by rw [hSq, ha]
  rw [hAeq] at hLS
  have hc0 : 0 ≤ ∑ f ∈ S, ‖c f‖ ^ 2 := Finset.sum_nonneg fun f _ => by positivity
  rcases eq_or_lt_of_le hSq0 with hz | hz
  · rw [← hz]; positivity
  · have h2 : Sq ^ 2 ≤ (∑ f ∈ S, ‖c f‖ ^ 2) * (C * Sq) :=
      hcs.trans (mul_le_mul_of_nonneg_left hLS hc0)
    have : Sq * Sq ≤ ((∑ f ∈ S, ‖c f‖ ^ 2) * C) * Sq := by nlinarith
    exact le_of_mul_le_mul_right (by linarith [this]) hz
