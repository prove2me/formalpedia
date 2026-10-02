-- Prove2me | solution 1 for BookSixth.hadamard_equality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T03:22:39.974179+00:00
-- url     : https://prove2.me/submissions/43ad71d2-7340-495e-97c2-29f1cf059799

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open BookSixth

/-!
# Hadamard's determinant inequality, equality case

Mathlib has neither Hadamard's inequality nor the equality case of the unweighted AM-GM
inequality needed for it.  Both are developed here in a private namespace.
-/

namespace HadamardDet

variable {ι : Type*} [Fintype ι]

theorem le_exp_sub_one (t : ℝ) : t ≤ Real.exp (t - 1) := by
  have h := Real.add_one_le_exp (t - 1)
  linarith

theorem lt_exp_sub_one {t : ℝ} (ht : t ≠ 1) : t < Real.exp (t - 1) := by
  have h : t - 1 ≠ 0 := fun hc => ht (by linarith)
  have := Real.add_one_lt_exp h
  linarith

/-- The normalised entries have mean shift summing to zero. -/
theorem sum_shift {l : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hsum : ∑ i, l i = Fintype.card ι * c) :
    ∑ i, (l i / c - 1) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem prod_exp_shift {l : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hsum : ∑ i, l i = Fintype.card ι * c) :
    ∏ i, Real.exp (l i / c - 1) = 1 := by
  rw [← Real.exp_sum, sum_shift hc hsum, Real.exp_zero]

theorem prod_div {l : ι → ℝ} {c : ℝ} (hc : 0 < c) :
    ∏ i, l i = (∏ i, (l i / c)) * c ^ Fintype.card ι := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  field_simp

/-- **AM–GM**, in the form: a family of nonnegative reals with mean `c` has product at most
`c ^ card`. -/
theorem prod_le_pow_of_sum_eq {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) {c : ℝ} (hc : 0 < c)
    (hsum : ∑ i, l i = Fintype.card ι * c) :
    ∏ i, l i ≤ c ^ Fintype.card ι := by
  classical
  have hkey : ∏ i, (l i / c) ≤ 1 := by
    calc ∏ i, (l i / c) ≤ ∏ i, Real.exp (l i / c - 1) :=
          Finset.prod_le_prod (fun i _ => div_nonneg (hl i) hc.le)
            (fun i _ => le_exp_sub_one _)
      _ = 1 := prod_exp_shift hc hsum
  rw [prod_div hc]
  nlinarith [hkey, pow_pos hc (Fintype.card ι), Finset.prod_nonneg
    (fun (i : ι) (_ : i ∈ Finset.univ) => div_nonneg (hl i) hc.le)]

/-- The equality case of AM–GM. -/
theorem eq_of_prod_eq_pow {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) {c : ℝ} (hc : 0 < c)
    (hsum : ∑ i, l i = Fintype.card ι * c) (heq : ∏ i, l i = c ^ Fintype.card ι) :
    ∀ i, l i = c := by
  classical
  intro i0
  by_contra hne
  -- all entries are positive, since the product is
  have hposprod : 0 < ∏ i, l i := by rw [heq]; exact pow_pos hc _
  have hpos : ∀ i, 0 < l i := by
    intro i
    rcases (hl i).lt_or_eq with h | h
    · exact h
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ i) h.symm) (ne_of_gt hposprod)
  -- the product of the normalised entries is strictly below one
  have hlt : l i0 / c < Real.exp (l i0 / c - 1) := by
    refine lt_exp_sub_one ?_
    intro hc1
    exact hne (by field_simp at hc1; linarith)
  have hstrict : ∏ i, (l i / c) < 1 := by
    calc ∏ i, (l i / c) < ∏ i, Real.exp (l i / c - 1) :=
          Finset.prod_lt_prod (fun i _ => div_pos (hpos i) hc)
            (fun i _ => le_exp_sub_one _) ⟨i0, Finset.mem_univ i0, hlt⟩
      _ = 1 := prod_exp_shift hc hsum
  rw [prod_div hc] at heq
  nlinarith [hstrict, pow_pos hc (Fintype.card ι)]

section Gram

variable {n : ℕ}

/-- The Gram matrix `Aᵀ A` of the columns of `A`. -/
noncomputable def gram (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := A.transpose * A

theorem gram_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    gram A i j = ∑ k, A k i * A k j := by
  simp [gram, Matrix.mul_apply]

theorem gram_posSemidef (A : Matrix (Fin n) (Fin n) ℝ) : (gram A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem gram_det (A : Matrix (Fin n) (Fin n) ℝ) : (gram A).det = (A.det) ^ 2 := by
  simp [gram, Matrix.det_mul, sq]

theorem gram_diag {A : Matrix (Fin n) (Fin n) ℝ} (hA : SignMatrix A) (i : Fin n) :
    gram A i i = (n : ℝ) := by
  rw [gram_apply]
  have : ∀ k : Fin n, A k i * A k i = 1 := by
    intro k; rcases hA k i with h | h <;> rw [h] <;> norm_num
  simp [this]

theorem rpow_half_sq (n : ℕ) : ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (by positivity)]
  norm_num

theorem abs_eq_rpow_iff {d : ℝ} {n : ℕ} :
    |d| = (n : ℝ) ^ ((n : ℝ) / 2) ↔ d ^ 2 = (n : ℝ) ^ n := by
  have ht : (0 : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  constructor
  · intro h
    rw [← sq_abs, h, rpow_half_sq]
  · intro h
    rw [← Real.sqrt_sq_eq_abs, h, ← rpow_half_sq n, Real.sqrt_sq ht]

end Gram

section Main

variable {n : ℕ}

theorem trace_gram {A : Matrix (Fin n) (Fin n) ℝ} (hA : SignMatrix A) :
    (gram A).trace = (n : ℝ) * (n : ℝ) := by
  rw [Matrix.trace]
  simp [Matrix.diag, gram_diag hA]

theorem sum_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : SignMatrix A) :
    ∑ i, (gram_posSemidef A).isHermitian.eigenvalues i
      = (Fintype.card (Fin n) : ℝ) * (n : ℝ) := by
  have h := Matrix.IsHermitian.trace_eq_sum_eigenvalues (gram_posSemidef A).isHermitian
  rw [trace_gram hA] at h
  simpa using h.symm

theorem prod_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) :
    ∏ i, (gram_posSemidef A).isHermitian.eigenvalues i = (A.det) ^ 2 := by
  have h := Matrix.IsHermitian.det_eq_prod_eigenvalues (gram_posSemidef A).isHermitian
  rw [gram_det] at h
  simpa using h.symm

/-- A Hermitian matrix all of whose eigenvalues equal `c` is `c • 1`. -/
theorem eq_smul_one_of_eigenvalues_const {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    {c : ℝ} (h : ∀ i, hM.eigenvalues i = c) :
    M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix (Fin n) (Fin n) ℝ)
      = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [h]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  conv_lhs => rw [hM.spectral_theorem]
  rw [hd, map_smul, map_one]

theorem hadamard_eq {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) :
    (|A.det| = (n : ℝ) ^ ((n : ℝ) / 2)) ↔ ∀ i j, i ≠ j → (∑ k, A k i * A k j) = 0 := by
  have hps := gram_posSemidef A
  have hH := hps.isHermitian
  have hcn : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    have hdet : (A.det) ^ 2 = (n : ℝ) ^ n := abs_eq_rpow_iff.mp h
    have hprod : ∏ i, hH.eigenvalues i = (n : ℝ) ^ Fintype.card (Fin n) := by
      rw [prod_eigenvalues, hdet]; simp
    have hall := eq_of_prod_eq_pow (fun i => hps.eigenvalues_nonneg i) hcn
      (sum_eigenvalues hA) hprod
    have hM : gram A = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
      eq_smul_one_of_eigenvalues_const hH hall
    intro i j hij
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hM
    simpa [gram_apply, Matrix.one_apply_ne hij] using he
  · intro h
    have hM : gram A = Matrix.diagonal (fun _ => (n : ℝ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [gram_diag hA]
      · rw [gram_apply, h i j hij, Matrix.diagonal_apply_ne _ hij]
    have hdet : (A.det) ^ 2 = (n : ℝ) ^ n := by
      rw [← gram_det, hM, Matrix.det_diagonal]
      simp
    exact abs_eq_rpow_iff.mpr hdet

end Main

end HadamardDet


open scoped BigOperators in
open BookSixth in
theorem solution {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) :
    (|A.det| = (n : ℝ) ^ ((n : ℝ) / 2)) ↔
      ∀ i j, i ≠ j → (∑ k, A k i * A k j) = 0 :=
  HadamardDet.hadamard_eq hn A hA
