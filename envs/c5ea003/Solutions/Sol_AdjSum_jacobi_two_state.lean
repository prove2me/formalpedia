-- Prove2me | solution 1 for AdjSum.jacobi_two_state
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:39:12.180028+00:00
-- url     : https://prove2.me/submissions/15d2bc08-1c78-4288-a161-12b476d3493e

-- Sol generated from Applications/AdjacentSumPolytopes/Recurrence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# Cayley–Hamilton recurrences and the shared characteristic denominator

Building on `Applications.AdjacentSumPolytopes.Basic`, where the open and cyclic
adjacent-sum lattice counts were identified with matrix entries and traces of powers
of the `(s+1)`-state transfer matrix `adjMat s`, we deduce:

* a **linear recurrence of order `s + 2`** satisfied by *both* the open counts and the
  cyclic counts, with coefficients the coefficients of the characteristic polynomial
  of the transfer matrix (`openCount_recurrence`, `cycCount_recurrence`);
* the resulting **shared characteristic denominator** for the two generating functions
  (`openSeries_mul_charDenom_isPoly`, `cycSeries_mul_charDenom_isPoly`): multiplying
  either formal power series by the *same* reciprocal characteristic polynomial
  `charDenom s` produces a polynomial of degree `≤ s`;
* the **Jacobi derivative identity** in the two-state case (`jacobi_two_state`):
  `(∑ₙ tr(Mⁿ) Xⁿ) · det(I − XM) = 2 − tr(M)·X = 2·p(X) − X·p'(X)` for `p = det(I − XM)`,
  which is the `k = 2` instance of `∑ₙ tr(Mⁿ)Xⁿ = (k·p − X p')/p`.

The general algebraic engine (`charpoly_pow_recurrence`, `charpoly_trace_recurrence`,
`charpoly_entry_recurrence`, `coeff_mul_revDenom`) is stated for arbitrary square
matrices over a commutative ring and for arbitrary linearly recurrent sequences, so it
applies verbatim to the `(s+2)`-state matrices of the lattice-polytope model.

-- !-- Lab Notes -- !--
* **Hypothesis.** Since the open counts are bilinear-form values `1ᵀ Mᵈ 1` and the
  cyclic counts are traces `tr Mᵈ`, Cayley–Hamilton should force *both* to obey the
  characteristic recurrence, i.e. the two Ehrhart-type series share a denominator.
* **Experiment.** For `s = 2` the characteristic polynomial of `adjMat 2` is
  `X³ − 2X² − X + 1`, and indeed both `3, 6, 14, 31, 70, 157, 353, 793` (open) and
  `2, 6, 11, 26, 57, 129, 289, 650` (cyclic) satisfy `a₍ₙ₊₃₎ = 2a₍ₙ₊₂₎ + a₍ₙ₊₁₎ − aₙ`:
  `31 = 2·14 + 6 − 3`, `70 = 2·31 + 14 − 6`, `26 = 2·11 + 6 − 2`, `57 = 2·26 + 11 − 6`.
  Computed characteristic polynomials (coefficients from the top): `s = 1 : (1,−1,−1)`,
  `s = 2 : (1,−2,−1,1)`, `s = 3 : (1,−2,−3,1,1)`, `s = 4 : (1,−3,−3,4,1,−1)`,
  `s = 5 : (1,−3,−6,4,5,−1,−1)` — the signs run in a period-four pattern `+,−,−,+`.
* **Analysis.** The recurrence survives with no positivity or irreducibility
  hypotheses whatsoever: it is pure Cayley–Hamilton.  What is *not* automatic is the
  numerator, which differs between the two parity classes; the two-state Jacobi
  identity pins it down for `k = 2`.
* **Critique.** `charpoly_pow_recurrence` needs `Nontrivial R` (for
  `charpoly_natDegree_eq_dim`); over the trivial ring everything is `0` anyway.  The
  power-series lemma is stated for `k ≤ m` — for `m < k` the coefficients are exactly
  the numerator and are generally nonzero, so the bound is sharp.
-/

open AdjSum

open Finset Matrix Polynomial PowerSeries

/-! ## Generic Cayley–Hamilton recurrences -/




/-! ## Generating functions of linearly recurrent sequences -/




/-! ## The integral transfer matrix -/





/-! ## Counting functions and their common recurrence -/







/-! ## The shared denominator of the two Ehrhart-type series -/








/-! ## The two-state Jacobi derivative identity -/

/-- Cayley–Hamilton for `2 × 2` matrices, proved entrywise (no `Nontrivial` needed). -/
theorem sq_eq_trace_smul_sub_det_smul {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.det_fin_two,
      Fin.sum_univ_two] <;> ring

/-- The trace sequence of a `2 × 2` matrix obeys the second-order recurrence
`tₙ₊₂ = (tr M) tₙ₊₁ − (det M) tₙ`. -/
theorem trace_pow_rec {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    Matrix.trace (M ^ (n + 2)) =
      M.trace * Matrix.trace (M ^ (n + 1)) - M.det * Matrix.trace (M ^ n) := by
  have h : M ^ (n + 2) = M.trace • M ^ (n + 1) - M.det • M ^ n := by
    have h2 : M ^ (n + 2) = M ^ n * M ^ 2 := by rw [← pow_add]
    rw [h2, sq_eq_trace_smul_sub_det_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
      mul_one, ← pow_succ]
  rw [h, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]




open AdjSum in
theorem solution{R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (PowerSeries.mk fun n => Matrix.trace (M ^ n)) *
        (1 - PowerSeries.C M.trace * PowerSeries.X
              + PowerSeries.C M.det * PowerSeries.X ^ 2)
      = PowerSeries.C 2 - PowerSeries.C M.trace * PowerSeries.X := by
  set A : PowerSeries R := PowerSeries.mk fun n => Matrix.trace (M ^ n) with hA
  have expand : A * (1 - PowerSeries.C M.trace * PowerSeries.X
        + PowerSeries.C M.det * PowerSeries.X ^ 2)
      = A - PowerSeries.C M.trace * (A * PowerSeries.X ^ 1)
          + PowerSeries.C M.det * (A * PowerSeries.X ^ 2) := by
    rw [pow_one]; ring
  rw [expand]
  ext n
  rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', hA]
  match n with
  | 0 => simp [Matrix.trace_one]
  | 1 => simp [Matrix.trace_one, pow_one]; ring
  | (n + 2) =>
      rw [if_pos (by omega), if_pos (by omega)]
      simp only [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_C_mul]
      have h1 : n + 2 - 1 = n + 1 := by omega
      have h2 : n + 2 - 2 = n := by omega
      rw [h1, h2, trace_pow_rec M n]
      simp [PowerSeries.coeff_X]
