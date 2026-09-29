-- Prove2me | solution 1 for HefferonLinAlg.row_equivalent_iff_same_row_space
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:52:58.302571+00:00
-- url     : https://prove2.me/submissions/0126bf1c-61fd-44a2-80af-e25ccdc2be63

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms

open Matrix

#check Submodule.span_induction
#check Submodule.exists_linearEquiv_restrict_eq
#check Submodule.quotEquivOfEq_mk
#check LinearMap.quotKerEquivRange_apply_mk
#check LinearMap.toMatrix'_mulVec
#check isUnit_iff_exists_inv

namespace HefferonLinAlg

theorem span_rows_mul_le {K : Type*} [Field K] {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
    Submodule.span K (Set.range (M * A)) ≤ Submodule.span K (Set.range A) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hrow : (M * A) i = ∑ j, M i j • A j := by
    funext c
    simp [Matrix.mul_apply]
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem ker_mulVec_le_of_span_rows_le {K : Type*} [Field K] {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) K)
    (hspan : Submodule.span K (Set.range B) ≤ Submodule.span K (Set.range A)) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker B.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  funext i
  change B i ⬝ᵥ x = 0
  have hb : B i ∈ Submodule.span K (Set.range A) :=
    hspan (Submodule.subset_span ⟨i, rfl⟩)
  refine Submodule.span_induction
    (p := fun y _ => y ⬝ᵥ x = 0)
    ?_ ?_ ?_ ?_ hb
  · intro y hy
    rcases hy with ⟨j, rfl⟩
    exact congrFun hx j
  · simp [dotProduct]
  · intro y z _ _ hy hz
    rw [add_dotProduct, hy, hz, add_zero]
  · intro c y _ hy
    rw [smul_dotProduct, hy, smul_zero]

theorem ker_mulVec_eq_of_span_rows_eq {K : Type*} [Field K] {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) K)
    (hspan : Submodule.span K (Set.range A) = Submodule.span K (Set.range B)) :
    LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin := by
  apply le_antisymm
  · exact ker_mulVec_le_of_span_rows_le A B hspan.ge
  · exact ker_mulVec_le_of_span_rows_le B A hspan.le

theorem exists_linearEquiv_comp_of_ker_eq
    {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (f g : V →ₗ[K] W) (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃ E : W ≃ₗ[K] W, ∀ x, E (f x) = g x := by
  let eRange : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
    f.quotKerEquivRange.symm ≪≫ₗ
      (LinearMap.ker f).quotEquivOfEq (LinearMap.ker g) hker ≪≫ₗ
        g.quotKerEquivRange
  obtain ⟨E, hE⟩ := Submodule.exists_linearEquiv_restrict_eq eRange
  refine ⟨E, fun x => ?_⟩
  have heval : ((eRange ⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range g) : W) = g x := by
    simp [eRange, LinearEquiv.trans_apply,
      LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivRange_apply_mk]
  exact (hE ⟨f x, ⟨x, rfl⟩⟩).symm.trans heval

theorem root_solution
    {K : Type*} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K) :
    (∃ M : Matrix (Fin m) (Fin m) K, IsUnit M.det ∧ B = M * A) ↔
      Submodule.span K (Set.range A) = Submodule.span K (Set.range B) := by
  classical
  constructor
  · rintro ⟨M, hM, rfl⟩
    apply le_antisymm
    · have hprod : M⁻¹ * (M * A) = A := by
        rw [← Matrix.mul_assoc, M.nonsing_inv_mul hM, Matrix.one_mul]
      calc
        Submodule.span K (Set.range A) =
            Submodule.span K (Set.range (M⁻¹ * (M * A))) := by rw [hprod]
        _ ≤ Submodule.span K (Set.range (M * A)) := span_rows_mul_le M⁻¹ (M * A)
    · exact span_rows_mul_le M A
  · intro hspan
    let f := A.mulVecLin
    let g := B.mulVecLin
    have hker : LinearMap.ker f = LinearMap.ker g := by
      exact ker_mulVec_eq_of_span_rows_eq A B hspan
    obtain ⟨E, hE⟩ := exists_linearEquiv_comp_of_ker_eq f g hker
    let M : Matrix (Fin m) (Fin m) K := E.toLinearMap.toMatrix'
    refine ⟨M, ?_, ?_⟩
    · apply M.isUnit_iff_isUnit_det.mp
      change IsUnit E.toLinearMap.toMatrix'
      rw [LinearMap.isUnit_toMatrix'_iff, isUnit_iff_exists_inv]
      refine ⟨E.symm.toLinearMap, ?_⟩
      ext x
      simp
    · apply Matrix.mulVec_injective
      funext x
      rw [← Matrix.mulVec_mulVec]
      simp only [M, LinearMap.toMatrix'_mulVec]
      simpa [f, g] using (hE x).symm

end HefferonLinAlg

theorem solution
    {K : Type*} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K) :
    (∃ M : Matrix (Fin m) (Fin m) K, IsUnit M.det ∧ B = M * A) ↔
      Submodule.span K (Set.range A) = Submodule.span K (Set.range B) :=
  HefferonLinAlg.root_solution A B
