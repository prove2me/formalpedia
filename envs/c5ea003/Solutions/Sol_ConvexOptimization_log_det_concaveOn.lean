-- Prove2me | solution 1 for ConvexOptimization.log_det_concaveOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-15T14:55:36.354362+00:00
-- url     : https://prove2.me/submissions/c85c5181-b17e-44a0-b971-cf16e2619298

import Mathlib

open Set
open scoped MatrixOrder

private lemma sqrt_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (CFC.sqrt A).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp (hA.isStrictlyPositive.sqrt A)

private lemma sqrt_inv_conj_posDef {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosDef := by
  let S := CFC.sqrt A
  have hS : S.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.sqrt A)
  have hSinv : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hS.isUnit
  have hstar : star S⁻¹ = S⁻¹ := hS.isHermitian.inv.eq
  simpa only [S, hstar] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff hSinv).2 hB

private lemma det_affine_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (a b : ℝ) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • C).det =
      ∏ i, (a + b * hC.isHermitian.eigenvalues i) := by
  let hH := hC.isHermitian
  let U := hH.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℝ _ U
  have hdiag :
      a • (1 : Matrix (Fin n) (Fin n) ℝ) +
          b • Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
        Matrix.diagonal (fun i => a + b * hH.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hconj :
      a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • C =
        E (Matrix.diagonal (fun i => a + b * hH.eigenvalues i)) := by
    have hspec : C = E (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
      hH.spectral_theorem
    calc
      a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • C =
          a • 1 + b • E (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        congrArg (fun X => a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • X) hspec
      _ = E (a • 1 + b • Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues)) := by
        symm
        simpa using E.map_add
          (a • (1 : Matrix (Fin n) (Fin n) ℝ))
          (b • Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues))
      _ = E (Matrix.diagonal (fun i => a + b * hH.eigenvalues i)) :=
        congrArg E hdiag
  rw [hconj]
  rw [show hC.isHermitian = hH by rfl]
  simp only [E, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_diagonal]
  rw [mul_assoc, mul_comm (∏ i, (a + b * hH.eigenvalues i)), ← mul_assoc]
  rw [← Matrix.det_mul]
  simp [U]

private lemma affine_eq_sqrt_conj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (a b : ℝ) :
    let S := CFC.sqrt A
    let C := S⁻¹ * B * S⁻¹
    a • A + b • B = S * (a • 1 + b • C) * S := by
  dsimp only
  let S := CFC.sqrt A
  have hS : S.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.sqrt A)
  letI := hS.isUnit.invertible
  have hsq : S * S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  change a • A + b • B =
    a • (S * 1 * S) + b • (S * (S⁻¹ * B * S⁻¹) * S)
  simp [Matrix.mul_assoc, hsq]

theorem solution {n : ℕ} :
    ConcaveOn ℝ {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}
      (fun A => Real.log A.det) := by
  rw [concaveOn_iff_forall_pos]
  refine ⟨?_, ?_⟩
  · rw [convex_iff_forall_pos]
    intro A hA B hB a b ha hb hab
    exact (hA.smul ha).add (hB.smul hb)
  · intro A hA B hB a b ha hb hab
    let S := CFC.sqrt A
    let C := S⁻¹ * B * S⁻¹
    have hS : S.PosDef := sqrt_posDef A hA
    have hC : C.PosDef := sqrt_inv_conj_posDef A B hA hB
    let eig : Fin n → ℝ := hC.isHermitian.eigenvalues
    have hsq : S * S = A := by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hdetA : A.det = S.det * S.det := by
      rw [← hsq, Matrix.det_mul]
    have hdet_factor (u v : ℝ) :
        (u • A + v • B).det = A.det * ∏ i, (u + v * eig i) := by
      rw [affine_eq_sqrt_conj A B hA u v]
      rw [Matrix.det_mul, Matrix.det_mul, det_affine_one C hC]
      rw [hdetA]
      ring
    have hdetB : B.det = A.det * ∏ i, eig i := by
      simpa using hdet_factor 0 1
    have hdetMix : (a • A + b • B).det =
        A.det * ∏ i, (a + b * eig i) := hdet_factor a b
    have heig (i : Fin n) : 0 < eig i := hC.eigenvalues_pos i
    have hmix (i : Fin n) : 0 < a + b * eig i :=
      add_pos ha (mul_pos hb (heig i))
    have hscalar (i : Fin n) :
        b * Real.log (eig i) ≤ Real.log (a + b * eig i) := by
      simpa using strictConcaveOn_log_Ioi.concaveOn.2
        (show (1 : ℝ) ∈ Ioi 0 by norm_num) (heig i) ha.le hb.le hab
    have hsum : b * ∑ i, Real.log (eig i) ≤
        ∑ i, Real.log (a + b * eig i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ hscalar i
    have hprodEig : 0 < ∏ i, eig i := Finset.prod_pos fun i _ ↦ heig i
    have hprodMix : 0 < ∏ i, (a + b * eig i) :=
      Finset.prod_pos fun i _ ↦ hmix i
    have hlogProdEig : Real.log (∏ i, eig i) = ∑ i, Real.log (eig i) :=
      Real.log_prod fun i _ ↦ (heig i).ne'
    have hlogProdMix : Real.log (∏ i, (a + b * eig i)) =
        ∑ i, Real.log (a + b * eig i) :=
      Real.log_prod fun i _ ↦ (hmix i).ne'
    simp only [smul_eq_mul]
    rw [hdetB, hdetMix]
    rw [Real.log_mul hA.det_pos.ne' hprodEig.ne',
      Real.log_mul hA.det_pos.ne' hprodMix.ne', hlogProdEig, hlogProdMix]
    calc
      a * Real.log A.det + b * (Real.log A.det + ∑ i, Real.log (eig i)) =
          Real.log A.det + b * ∑ i, Real.log (eig i) := by
        calc
          _ = (a + b) * Real.log A.det + b * ∑ i, Real.log (eig i) := by ring
          _ = _ := by rw [hab, one_mul]
      _ ≤ Real.log A.det + ∑ i, Real.log (a + b * eig i) :=
        by simpa only [add_comm] using add_le_add_left hsum (Real.log A.det)
