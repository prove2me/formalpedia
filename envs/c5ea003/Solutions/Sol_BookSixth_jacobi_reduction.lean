-- Prove2me | solution 1 for BookSixth.jacobi_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T01:06:08.588467+00:00
-- url     : https://prove2.me/submissions/8f7b2395-dedf-4887-bffb-b3d26c21fdbe

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

variable {n : ℕ}

theorem sum_two (p q : Fin n) (hpq : p ≠ q) (f : Fin n → ℝ)
    (h : ∀ k, k ≠ p → k ≠ q → f k = 0) : ∑ k, f k = f p + f q := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset (Fin n)))]
  · rw [Finset.sum_pair hpq]
  · intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact h k hk.1 hk.2

/-- The Givens rotation in the `(p,q)` plane. -/
def givens (p q : Fin n) (c s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if j = p then (if i = p then c else if i = q then s else 0)
    else if j = q then (if i = p then -s else if i = q then c else 0)
    else if i = j then 1 else 0

variable {p q : Fin n} {c s : ℝ}

theorem givens_col_p (hpq : p ≠ q) (X : Fin n → ℝ) :
    ∑ k, givens p q c s k p * X k = c * X p + s * X q := by
  rw [sum_two p q hpq]
  · simp [givens, hpq, Ne.symm hpq]
  · intro k hk1 hk2
    simp [givens, hk1, hk2]

theorem givens_col_q (hpq : p ≠ q) (X : Fin n → ℝ) :
    ∑ k, givens p q c s k q * X k = -s * X p + c * X q := by
  rw [sum_two p q hpq]
  · simp [givens, hpq, Ne.symm hpq]
  · intro k hk1 hk2
    simp [givens, hk1, hk2, Ne.symm hpq]

theorem givens_col_other (hpq : p ≠ q) {j : Fin n} (hj1 : j ≠ p) (hj2 : j ≠ q) (X : Fin n → ℝ) :
    ∑ k, givens p q c s k j * X k = X j := by
  classical
  rw [Finset.sum_eq_single j]
  · simp [givens, hj1, hj2]
  · intro k _ hk
    simp [givens, hj1, hj2, hk]
  · intro h; exact absurd (Finset.mem_univ j) h


theorem star_givens (a b : Fin n) :
    (star (givens p q c s) : Matrix (Fin n) (Fin n) ℝ) a b = givens p q c s b a := rfl

theorem givens_row_p (hpq : p ≠ q) (j : Fin n) :
    ∑ k, givens p q c s k p * givens p q c s k j
      = c * givens p q c s p j + s * givens p q c s q j :=
  givens_col_p hpq _

theorem givens_unitary (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1) :
    star (givens p q c s) * givens p q c s = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [star_givens]
  rw [Matrix.one_apply]
  by_cases hi : i = p
  · subst hi
    rw [givens_col_p hpq]
    by_cases hj : j = i
    · subst hj; simp [givens, hpq, Ne.symm hpq]; nlinarith [hcs]
    · by_cases hjq : j = q
      · subst hjq; simp [givens, hpq, Ne.symm hpq, hj]; ring
      · simp [givens, hj, hjq, Ne.symm hj, Ne.symm hjq, hpq, Ne.symm hpq]
  · by_cases hiq : i = q
    · subst hiq
      rw [givens_col_q hpq]
      by_cases hj : j = i
      · subst hj; simp [givens, hpq, Ne.symm hpq, hi]; nlinarith [hcs]
      · by_cases hjp : j = p
        · subst hjp; simp [givens, hpq, Ne.symm hpq, hj]; ring
        · simp [givens, hj, hjp, Ne.symm hj, Ne.symm hjp, hpq, Ne.symm hpq]
    · rw [givens_col_other hpq hi hiq]
      by_cases hj : j = i
      · subst hj; simp [givens, hi, hiq]
      · by_cases hjp : j = p
        · subst hjp; simp [givens, hi, hiq, Ne.symm hj]
        · by_cases hjq : j = q
          · subst hjq; simp [givens, hi, hiq, Ne.symm hj]
          · simp [givens, hi, hiq, hjp, hjq, Ne.symm hj]


theorem conj_entry (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (star (givens p q c s) * A * givens p q c s) i j
      = ∑ l, givens p q c s l j * (∑ k, givens p q c s k i * A k l) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, mul_comm]
  rfl

theorem conj_pp (hpq : p ≠ q) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A q p = A p q) :
    (star (givens p q c s) * A * givens p q c s) p p
      = c ^ 2 * A p p + 2 * c * s * A p q + s ^ 2 * A q q := by
  rw [conj_entry]
  have hin : ∀ l, (∑ k, givens p q c s k p * A k l) = c * A p l + s * A q l :=
    fun l => givens_col_p hpq (fun k => A k l)
  simp only [hin]
  rw [givens_col_p hpq (fun l => c * A p l + s * A q l), hA]
  ring

theorem conj_qq (hpq : p ≠ q) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A q p = A p q) :
    (star (givens p q c s) * A * givens p q c s) q q
      = s ^ 2 * A p p - 2 * c * s * A p q + c ^ 2 * A q q := by
  rw [conj_entry]
  have hin : ∀ l, (∑ k, givens p q c s k q * A k l) = -s * A p l + c * A q l :=
    fun l => givens_col_q hpq (fun k => A k l)
  simp only [hin]
  rw [givens_col_q hpq (fun l => -s * A p l + c * A q l), hA]
  ring

theorem conj_pq (hpq : p ≠ q) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A q p = A p q) :
    (star (givens p q c s) * A * givens p q c s) p q
      = (c ^ 2 - s ^ 2) * A p q - c * s * (A p p - A q q) := by
  rw [conj_entry]
  have hin : ∀ l, (∑ k, givens p q c s k p * A k l) = c * A p l + s * A q l :=
    fun l => givens_col_p hpq (fun k => A k l)
  simp only [hin]
  rw [givens_col_q hpq (fun l => c * A p l + s * A q l), hA]
  ring

theorem conj_ii (hpq : p ≠ q) (A : Matrix (Fin n) (Fin n) ℝ) {i : Fin n}
    (hi1 : i ≠ p) (hi2 : i ≠ q) :
    (star (givens p q c s) * A * givens p q c s) i i = A i i := by
  rw [conj_entry]
  have hin : ∀ l, (∑ k, givens p q c s k i * A k l) = A i l :=
    fun l => givens_col_other hpq hi1 hi2 (fun k => A k l)
  simp only [hin]
  exact givens_col_other hpq hi1 hi2 (fun l => A i l)


theorem frob_trace (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (star M * M) = ∑ j, ∑ i, (M i j) ^ 2 := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (M i j) * (M i j) = (M i j) ^ 2
  ring

theorem frob_conj (Q A : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * star Q = 1) :
    Matrix.trace (star (star Q * A * Q) * (star Q * A * Q)) = Matrix.trace (star A * A) := by
  have h1 : star (star Q * A * Q) = star Q * star A * Q := by
    rw [star_mul, star_mul, star_star]
    noncomm_ring
  have hrw : star (star Q * A * Q) * (star Q * A * Q) = star Q * (star A * A) * Q := by
    rw [h1]
    calc star Q * star A * Q * (star Q * A * Q)
        = star Q * star A * (Q * star Q) * A * Q := by noncomm_ring
      _ = star Q * (star A * A) * Q := by rw [hQ]; noncomm_ring
  rw [hrw, mul_assoc, Matrix.trace_mul_comm, mul_assoc, hQ, mul_one]

theorem sum_off (f : Fin n → ℝ) (i : Fin n) :
    ∑ j, (if i = j then (0:ℝ) else f j) = (∑ j, f j) - f i := by
  have hstep : ∀ j, (if i = j then (0:ℝ) else f j) = f j - (if i = j then f j else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

theorem offDiag_eq (M : Matrix (Fin n) (Fin n) ℝ) :
    offDiagonalMass M = (∑ i, ∑ j, (M i j) ^ 2) - ∑ i, (M i i) ^ 2 := by
  unfold offDiagonalMass
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => sum_off (fun j => (M i j) ^ 2) i

theorem frob_swap (M : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ i, (M i j) ^ 2 = ∑ i, ∑ j, (M i j) ^ 2 := Finset.sum_comm


/-- Chapter 7, the Jacobi reduction lemma. -/
theorem jacobi_reduction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (h : 0 < offDiagonalMass A) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℝ,
      offDiagonalMass (star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ))
        < offDiagonalMass A := by
  classical
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have := hA.apply i j
    simpa using this
  obtain ⟨p, q, hpq, hApq⟩ : ∃ p q : Fin n, p ≠ q ∧ A p q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : offDiagonalMass A = 0 := by
      unfold offDiagonalMass
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, hcon i j hij]
    linarith
  set D : ℝ := (A p p - A q q) / 2 with hD
  set R : ℝ := Real.sqrt ((A p q) ^ 2 + D ^ 2) with hR
  have hRsq : R ^ 2 = (A p q) ^ 2 + D ^ 2 := Real.sq_sqrt (by positivity)
  have hRpos : 0 < R := by
    rw [hR]
    apply Real.sqrt_pos.2
    positivity
  have hRD : 0 < R + D := by
    nlinarith [hRsq, hRpos, sq_nonneg (A p q), sq_abs (A p q), pow_pos (abs_pos.2 hApq) 2]
  set c : ℝ := Real.sqrt ((R + D) / (2 * R)) with hc
  have hcsq : c ^ 2 = (R + D) / (2 * R) := Real.sq_sqrt (by positivity)
  have hcpos : 0 < c := by
    rw [hc]; apply Real.sqrt_pos.2; positivity
  set s : ℝ := A p q / (2 * R * c) with hs
  have hssq : s ^ 2 = (R - D) / (2 * R) := by
    rw [hs, div_pow, mul_pow, mul_pow, hcsq]
    field_simp
    nlinarith [hRsq]
  have hcs1 : c ^ 2 + s ^ 2 = 1 := by
    rw [hcsq, hssq]; field_simp; ring
  have hcsprod : c * s = A p q / (2 * R) := by
    rw [hs]; field_simp
  -- the rotation
  set G : Matrix (Fin n) (Fin n) ℝ := givens p q c s with hG
  have hGU : star G * G = 1 := givens_unitary hpq hcs1
  have hGU' : G * star G = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin n))).1 hGU
  set B : Matrix (Fin n) (Fin n) ℝ := star G * A * G with hB
  have hBpq : B p q = 0 := by
    rw [hB, conj_pq hpq A (hsym p q)]
    have h1 : c ^ 2 - s ^ 2 = D / R := by rw [hcsq, hssq]; field_simp; ring
    have h2 : A p p - A q q = 2 * D := by rw [hD]; ring
    rw [h1, h2, hcsprod]
    field_simp
    ring
  have hBp : B p p = c ^ 2 * A p p + 2 * c * s * A p q + s ^ 2 * A q q := by
    rw [hB]; exact conj_pp hpq A (hsym p q)
  have hBq : B q q = s ^ 2 * A p p - 2 * c * s * A p q + c ^ 2 * A q q := by
    rw [hB]; exact conj_qq hpq A (hsym p q)
  have hBo : B p q = (c ^ 2 - s ^ 2) * A p q - c * s * (A p p - A q q) := by
    rw [hB]; exact conj_pq hpq A (hsym p q)
  have hBsum : B p p + B q q = A p p + A q q := by
    rw [hBp, hBq]
    linear_combination (A p p + A q q) * hcs1
  have hBsq : B p p ^ 2 + B q q ^ 2 = A p p ^ 2 + A q q ^ 2 + 2 * (A p q) ^ 2 := by
    have hdet : B p p * B q q - (B p q) ^ 2
        = (c ^ 2 + s ^ 2) ^ 2 * (A p p * A q q - (A p q) ^ 2) := by
      rw [hBp, hBq, hBo]; ring
    rw [hcs1, hBpq] at hdet
    linear_combination (B p p + B q q + A p p + A q q) * hBsum - 2 * hdet
  have hdiag : ∀ i, i ≠ p → i ≠ q → B i i = A i i := fun i h1 h2 => by
    rw [hB]; exact conj_ii hpq A h1 h2
  -- the diagonal mass strictly increases
  have hdsum : ∑ i, (B i i) ^ 2 = (∑ i, (A i i) ^ 2) + 2 * (A p q) ^ 2 := by
    have hsplit : ∀ (f : Fin n → ℝ), ∑ i, f i
        = f p + f q + ∑ i ∈ Finset.univ \ {p, q}, f i := by
      intro f
      rw [← Finset.sum_pair hpq, ← Finset.sum_sdiff (Finset.subset_univ ({p, q} : Finset (Fin n)))]
      ring
    rw [hsplit (fun i => (B i i) ^ 2), hsplit (fun i => (A i i) ^ 2)]
    have hrest : ∑ i ∈ Finset.univ \ {p, q}, (B i i) ^ 2
        = ∑ i ∈ Finset.univ \ {p, q}, (A i i) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [hdiag i hi.2.1 hi.2.2]
    rw [hrest]
    linarith [hBsq]
  -- Frobenius mass is preserved
  have hfrob : ∑ i, ∑ j, (B i j) ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
    have h1 := frob_conj G A hGU'
    rw [frob_trace, frob_trace] at h1
    rw [← frob_swap B, ← frob_swap A]
    exact h1
  refine ⟨⟨G, ⟨hGU, hGU'⟩⟩, ?_⟩
  show offDiagonalMass B < offDiagonalMass A
  rw [offDiag_eq, offDiag_eq, hfrob, hdsum]
  nlinarith [pow_pos (abs_pos.2 hApq) 2, sq_abs (A p q)]

end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (h : 0 < offDiagonalMass A) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℝ,
      offDiagonalMass (star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ))
        < offDiagonalMass A :=
  BookFix.jacobi_reduction A hA h
