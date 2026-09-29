-- Prove2me | solution 1 for AdjSum.openCount_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:15:01.820465+00:00
-- url     : https://prove2.me/submissions/b912c254-2b9c-4279-9a4e-f5ededd049bd

-- Sol generated from Applications/AdjacentSumPolytopes/Recurrence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence
import Theorems.Thm_AdjSum_card_openSet

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

/-- Cayley–Hamilton in "shifted" form: the matrix powers `M ^ (m + i)` satisfy the
linear recurrence given by the coefficients of the characteristic polynomial. -/
theorem charpoly_pow_recurrence {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (m : ℕ) :
    ∑ i ∈ Finset.range (n + 1), M.charpoly.coeff i • M ^ (m + i) = 0 := by
  have h0 : (Polynomial.aeval M) M.charpoly = 0 := Matrix.aeval_self_charpoly M
  have hdeg : M.charpoly.natDegree = n := by
    rw [M.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
  calc ∑ i ∈ Finset.range (n + 1), M.charpoly.coeff i • M ^ (m + i)
      = (∑ i ∈ Finset.range (n + 1), M.charpoly.coeff i • M ^ i) * M ^ m := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_mul_assoc, ← pow_add, add_comm i m]
    _ = 0 := by rw [h0, zero_mul]


/-- Every fixed matrix entry of the powers of a matrix satisfies the characteristic
recurrence. -/
theorem charpoly_entry_recurrence {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (m : ℕ) (a b : Fin n) :
    ∑ i ∈ Finset.range (n + 1), M.charpoly.coeff i * ((M ^ (m + i)) a b) = 0 := by
  have h := congrFun (congrFun (charpoly_pow_recurrence M m) a) b
  simpa [Matrix.sum_apply, smul_eq_mul] using h

/-! ## Generating functions of linearly recurrent sequences -/




/-! ## The integral transfer matrix -/


lemma adjMatZ_eq_map (s : ℕ) :
    adjMatZ s = (Nat.castRingHom ℤ).mapMatrix (adjMat s) := by
  ext a b
  simp only [adjMatZ, RingHom.mapMatrix_apply, Matrix.map_apply, adjMat,
    Nat.castRingHom]
  split <;> simp

lemma adjMatZ_pow_apply (s d : ℕ) (a b : Fin (s + 1)) :
    ((adjMatZ s) ^ d) a b = (((adjMat s ^ d) a b : ℕ) : ℤ) := by
  rw [adjMatZ_eq_map, ← map_pow]
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]


/-! ## Counting functions and their common recurrence -/



lemma openCount_eq (s d : ℕ) :
    (openCount s d : ℤ) = ∑ a, ∑ b, ((adjMatZ s) ^ d) a b := by
  simp [openCount, card_openSet, adjMatZ_pow_apply]




/-! ## The shared denominator of the two Ehrhart-type series -/








/-! ## The two-state Jacobi derivative identity -/






open AdjSum in
theorem solution(s m : ℕ) :
    ∑ i ∈ Finset.range (s + 2), (adjMatZ s).charpoly.coeff i * (openCount s (m + i) : ℤ) = 0 := by
  have key : ∀ i ∈ Finset.range (s + 2),
      (adjMatZ s).charpoly.coeff i * (openCount s (m + i) : ℤ)
        = ∑ a, ∑ b, (adjMatZ s).charpoly.coeff i * ((adjMatZ s) ^ (m + i)) a b := by
    intro i _
    rw [openCount_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum])
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  exact charpoly_entry_recurrence (adjMatZ s) m a b
