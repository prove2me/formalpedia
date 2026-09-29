-- Prove2me | solution 1 for LinearOptimization.farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:48:39.574467+00:00
-- url     : https://prove2.me/submissions/d03fc646-a498-4331-9840-ecdc129553b4

import Theorems.Thm_LinearOptimization_polyhedron_linear_image
import Theorems.Thm_LinearOptimization_polyhedron_closed
import Theorems.Thm_LinearOptimization_separating_hyperplane_polyhedron
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Xor' (∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ p : Fin m → ℝ, 0 ≤ Aᵀ.mulVec p ∧ p ⬝ᵥ b < 0) := by
  classical
  let C : Set (Fin m → ℝ) := A.mulVec '' {x : Fin n → ℝ | 0 ≤ x}
  have horthant :
      LinearOptimization.polyhedron (1 : Matrix (Fin n) (Fin n) ℝ) 0 =
        {x : Fin n → ℝ | 0 ≤ x} := by
    ext x
    simp [LinearOptimization.polyhedron, Pi.le_def]
  obtain ⟨r, D, e, himage⟩ :=
    LinearOptimization.polyhedron_linear_image
      (1 : Matrix (Fin n) (Fin n) ℝ) 0 A
  have hCpoly : C = LinearOptimization.polyhedron D e := by
    simpa [C, horthant] using himage
  have hCclosed : IsClosed C := by
    rw [hCpoly]
    exact LinearOptimization.polyhedron_closed D e
  let T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := A.mulVec
      map_add' := A.mulVec_add
      map_smul' := A.mulVec_smul }
  have hCconv : Convex ℝ C := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a c ha hc hac
    refine ⟨a • x + c • y, ?_, ?_⟩
    · intro j
      exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hc (hy j))
    · simp [T, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hCzero : (0 : Fin m → ℝ) ∈ C := by
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  have hdual (p : Fin m → ℝ) (x : Fin n → ℝ) :
      p ⬝ᵥ A.mulVec x = Aᵀ.mulVec p ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  by_cases hbC : b ∈ C
  · left
    constructor
    · rcases hbC with ⟨x, hx, hAx⟩
      exact ⟨x, hx, hAx⟩
    · rintro ⟨p, hp, hpb⟩
      rcases hbC with ⟨x, hx, hAx⟩
      have hnonneg : 0 ≤ Aᵀ.mulVec p ⬝ᵥ x := by
        exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (hp j) (hx j)
      rw [← hdual, hAx] at hnonneg
      linarith
  · right
    constructor
    · obtain ⟨p, hsep⟩ :=
        LinearOptimization.separating_hyperplane_polyhedron
          C ⟨0, hCzero⟩ hCclosed hCconv b hbC
      have hpb : p ⬝ᵥ b < 0 := by
        simpa using hsep 0 hCzero
      refine ⟨p, ?_, hpb⟩
      intro j
      by_contra hj
      have hq : Aᵀ.mulVec p j < 0 := lt_of_not_ge hj
      let q : ℝ := Aᵀ.mulVec p j
      let z : Fin n → ℝ :=
        (p ⬝ᵥ b / q + 1) • Pi.single j 1
      have hscale : 0 < p ⬝ᵥ b / q + 1 := by
        have : 0 < p ⬝ᵥ b / q := div_pos_of_neg_of_neg hpb (by simpa [q] using hq)
        linarith
      have hz : 0 ≤ z := by
        intro l
        simp only [z, Pi.smul_apply, smul_eq_mul]
        apply mul_nonneg hscale.le
        by_cases hlj : l = j <;> simp [Pi.single_apply, hlj]
      have hAz : A.mulVec z ∈ C := ⟨z, hz, rfl⟩
      have hs := hsep (A.mulVec z) hAz
      have heval : Aᵀ.mulVec p ⬝ᵥ z =
          (p ⬝ᵥ b / q + 1) * q := by
        simp [z, q, dotProduct, Pi.single_apply, mul_comm]
      rw [hdual, heval] at hs
      have hlt : (p ⬝ᵥ b / q + 1) * q < p ⬝ᵥ b := by
        have hqne : q ≠ 0 := ne_of_lt (by simpa [q] using hq)
        field_simp [hqne]
        linarith [hq]
      linarith
    · rintro ⟨x, hx, hAx⟩
      exact hbC ⟨x, hx, hAx⟩
