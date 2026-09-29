-- Prove2me | solution 1 for mme_bigAdd_map_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:20:27.35914+00:00
-- url     : https://prove2.me/submissions/6b6a7f42-ca48-4adf-87bc-9b45b11721ff

import Definitions.Def_mme_tensor_quotient
import Mathlib.Tactic

open MME PiTensorProduct BigOperators

universe u

namespace MME.DWZGluing

variable {K : Type u} [Field K]

/-- Fold a recursively represented tensor direct sum into common mode spaces,
using one linear map from each summand. -/
private noncomputable def bigAddFold
    {d : ℕ} {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    (k : ℕ) → (X : Fin k → TensorObj K d) →
      (∀ j i, (X j).V i →ₗ[K] W i) →
      ∀ i, (TensorObj.bigAdd X).V i →ₗ[K] W i
  | 0, _, _, _ => 0
  | 1, _, f, i => f 0 i
  | n + 2, X, f, i =>
      (f 0 i).coprod
        (bigAddFold (n + 1) (fun j => X j.succ)
          (fun j i => f j.succ i) i)

private theorem map_bigAddFold
    {d k : ℕ} {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (X : Fin k → TensorObj K d)
    (f : ∀ j i, (X j).V i →ₗ[K] W i) :
    PiTensorProduct.map (bigAddFold k X f) (TensorObj.bigAdd X).t =
      ∑ j : Fin k, PiTensorProduct.map (f j) (X j).t := by
  induction k with
  | zero =>
      change PiTensorProduct.map (fun _ => (0 : PUnit →ₗ[K] _)) 0 = 0
      simp
  | succ k ih =>
      cases k with
      | zero =>
          rw [Fin.sum_univ_one]
          change PiTensorProduct.map (f 0) (X 0).t = _
          rfl
      | succ n =>
          let tail : Fin (n + 1) → TensorObj K d := fun j => X j.succ
          let tailMap : ∀ j i, (tail j).V i →ₗ[K] W i :=
            fun j i => f j.succ i
          have hleft :
              (fun i =>
                bigAddFold (n + 2) X f i ∘ₗ
                  LinearMap.inl K ((X 0).V i)
                    ((TensorObj.bigAdd tail).V i)) = f 0 := by
            funext i
            simp only [bigAddFold]
            exact LinearMap.coprod_inl _ _
          have hright :
              (fun i =>
                bigAddFold (n + 2) X f i ∘ₗ
                  LinearMap.inr K ((X 0).V i)
                    ((TensorObj.bigAdd tail).V i)) =
                bigAddFold (n + 1) tail tailMap := by
            funext i
            simp only [bigAddFold]
            exact LinearMap.coprod_inr _ _
          let inlMap : ∀ i, (X 0).V i →ₗ[K]
              (TensorObj.bigAdd X).V i := fun i =>
            LinearMap.inl K ((X 0).V i) ((TensorObj.bigAdd tail).V i)
          let inrMap : ∀ i, (TensorObj.bigAdd tail).V i →ₗ[K]
              (TensorObj.bigAdd X).V i := fun i =>
            LinearMap.inr K ((X 0).V i) ((TensorObj.bigAdd tail).V i)
          change PiTensorProduct.map (bigAddFold (n + 2) X f)
              (PiTensorProduct.map inlMap (X 0).t +
                PiTensorProduct.map inrMap (TensorObj.bigAdd tail).t) = _
          calc
            _ = PiTensorProduct.map (bigAddFold (n + 2) X f)
                  (PiTensorProduct.map inlMap (X 0).t) +
                PiTensorProduct.map (bigAddFold (n + 2) X f)
                  (PiTensorProduct.map inrMap (TensorObj.bigAdd tail).t) := by
                    exact LinearMap.map_add _ _ _
            _ = PiTensorProduct.map (f 0) (X 0).t +
                PiTensorProduct.map (bigAddFold (n + 1) tail tailMap)
                  (TensorObj.bigAdd tail).t := by
                    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
                      ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
                    change
                      PiTensorProduct.map
                          (fun i => bigAddFold (n + 2) X f i ∘ₗ
                            LinearMap.inl K ((X 0).V i)
                              ((TensorObj.bigAdd tail).V i))
                          (X 0).t +
                        PiTensorProduct.map
                          (fun i => bigAddFold (n + 2) X f i ∘ₗ
                            LinearMap.inr K ((X 0).V i)
                              ((TensorObj.bigAdd tail).V i))
                          (TensorObj.bigAdd tail).t = _
                    rw [hleft, hright]
            _ = PiTensorProduct.map (f 0) (X 0).t +
                ∑ j : Fin (n + 1),
                  PiTensorProduct.map (tailMap j) (tail j).t := by
                    rw [ih tail tailMap]
            _ = ∑ j : Fin (n + 2),
                PiTensorProduct.map (f j) (X j).t := by
                  simpa [tail, tailMap] using
                    (Fin.sum_univ_succ
                      (fun j : Fin (n + 2) =>
                        PiTensorProduct.map (f j) (X j).t)).symm

end MME.DWZGluing

open MME

theorem solution
    {K : Type u} [Field K] {d s : ℕ}
    (X : Fin s → TensorObj K d)
    {W : Fin d → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module.Finite K (W i)]
    (f : ∀ j i, (X j).V i →ₗ[K] W i) :
    TensorObj.Restrict
      ({ V := W
         t := ∑ j, PiTensorProduct.map (f j) (X j).t } : TensorObj K d)
      (TensorObj.bigAdd X) := by
  refine ⟨MME.DWZGluing.bigAddFold s X f, ?_⟩
  exact MME.DWZGluing.map_bigAddFold X f
