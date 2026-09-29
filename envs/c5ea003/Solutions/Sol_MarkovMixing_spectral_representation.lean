-- Prove2me | solution 1 for MarkovMixing.spectral_representation
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T15:43:54.786951+00:00
-- url     : https://prove2.me/submissions/ea753f3c-4ef4-4584-88bb-75aed5112d02

import Definitions.Def_mm_spectral
import Mathlib.Analysis.Matrix.Spectrum

open MarkovMixing
open scoped BigOperators

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  classical
  set s : V → ℝ := fun x => Real.sqrt (π x) with hs_def
  have hs : ∀ x, 0 < s x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hs2 : ∀ x, s x * s x = π x := fun x => Real.mul_self_sqrt (hpos x).le
  -- the symmetrized matrix
  set A : Matrix V V ℝ := Matrix.of (fun x y => s x * P x y / s y) with hA_def
  have hAxy : ∀ x y, A x y = s x * P x y / s y := fun _ _ => rfl
  have hA : A.IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, star_trivial, hAxy]
    rw [div_eq_div_iff (hs x).ne' (hs y).ne']
    have h1 := hs2 x
    have h2 := hs2 y
    have h3 := hrev x y
    linear_combination P y x * h2 - P x y * h1 - h3
  set U : Matrix V V ℝ := (hA.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set lamV : V → ℝ := hA.eigenvalues with hlamV_def
  have hUstar : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUstar' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal lamV * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have : (RCLike.ofReal ∘ lamV) = lamV := by
      funext i; simp [RCLike.ofReal_real_eq_id]
    rw [this] at h
    simpa [hU_def, Unitary.coe_star] using h
  have hpow : ∀ t : ℕ, A ^ t = U * Matrix.diagonal (fun i => lamV i ^ t) * star U := by
    intro t
    induction t with
    | zero => simp [Matrix.diagonal_one, hUstar']
    | succ t ih =>
      rw [pow_succ, ih, hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUstar, Matrix.one_mul]
      rw [← Matrix.mul_assoc (Matrix.diagonal fun i => lamV i ^ t) (Matrix.diagonal lamV),
        Matrix.diagonal_mul_diagonal]
      congr 2
  have hcol : ∀ (i x : V), ∑ y, A x y * U y i = lamV i * U x i := by
    intro i x
    have h := congrFun (hA.mulVec_eigenvectorBasis i) x
    simpa [Matrix.mulVec, dotProduct, hU_def, hlamV_def,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hApow : ∀ (t : ℕ) (x y : V), (A ^ t) x y = s x * (P ^ t) x y / s y := by
    intro t
    induction t with
    | zero =>
      intro x y
      by_cases h : x = y
      · subst h; simp [Matrix.one_apply, (hs x).ne']
      · simp [Matrix.one_apply, h]
    | succ t ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ih x z, hAxy]
      have hz := (hs z).ne'
      have hy := (hs y).ne'
      field_simp
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with he_def
  refine ⟨fun j => lamV (e j), fun j x => U x (e j) / s x, ?_, ?_, ?_⟩
  · intro j
    funext x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hstep : ∀ y : V, P x y * (U y (e j) / s y) = A x y * U y (e j) / s x := by
      intro y
      rw [hAxy]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hstep y), ← Finset.sum_div,
      hcol (e j) x]
    ring
  · intro j k
    have h1 : innerPi π (fun x => U x (e j) / s x) (fun x => U x (e k) / s x)
        = ∑ x, U x (e j) * U x (e k) := by
      unfold innerPi
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hs2 x]
      have hx := (hs x).ne'
      field_simp
    have h2 : ∑ x, U x (e j) * U x (e k) = (star U * U) (e j) (e k) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.star_apply, star_trivial]
    rw [h1, h2, hUstar, Matrix.one_apply]
    simp [he_def]
  · intro t x y
    have hAt : (A ^ t) x y = ∑ i, U x i * U y i * lamV i ^ t := by
      rw [hpow t, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
      ring
    have hxy : (P ^ t) x y / π y = ((A ^ t) x y) / (s x * s y) := by
      rw [hApow t x y, ← hs2 y]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [hxy, hAt, Finset.sum_div]
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro j
    have hx := (hs x).ne'
    have hy := (hs y).ne'
    field_simp

