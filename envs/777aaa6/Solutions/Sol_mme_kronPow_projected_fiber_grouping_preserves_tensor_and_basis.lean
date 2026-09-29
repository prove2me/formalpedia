-- Prove2me | solution 1 for mme_kronPow_projected_fiber_grouping_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:16:32.841523+00:00
-- url     : https://prove2.me/submissions/41076098-57a0-4538-9ff1-c1e856af0c82

import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
open MME Module PiTensorProduct
universe u
set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {N k : ℕ} (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (count : Fin k → ℕ) (positions : Fin N ≃ (Σ c, Fin (count c)))
    (allowed : ∀ c i, (Fin (count c) → I i) → Prop) :
    let U := TensorObj.kronFin k (fun c ↦ T.kronPow (count c))
    let B := fun i ↦ TensorObj.kronPowModeWordBasis T i (b i) N
    let C := fun i ↦ TensorObj.kronFinModePiBasis k
      (fun c ↦ T.kronPow (count c)) i
      (fun c ↦ TensorObj.kronPowModeWordBasis T i (b i) (count c))
    let P := fun i (w : Fin N → I i) ↦
      ∀ c, allowed c i (fun r ↦ w (positions.symm ⟨c, r⟩))
    let Q := fun i (w : ∀ c, Fin (count c) → I i) ↦ ∀ c, allowed c i (w c)
    ∃ f : ∀ i, ((T.kronPow N).basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K]
        (U.basisAllAllowedGrading C Q).classOf i 0,
      PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
        ((T.kronPow N).basisAllAllowedSubtensor B P).t =
          (U.basisAllAllowedSubtensor C Q).t ∧
      ∀ i w, f i (((T.kronPow N).basisAllAllowedGrading B P).blockProj i 0
        (B i w)) =
        (U.basisAllAllowedGrading C Q).blockProj i 0
          (C i (fun c r ↦ w (positions.symm ⟨c, r⟩))) := by
  classical
  dsimp only
  obtain ⟨e, ht, hb⟩ :=
    mme_kronPow_fiber_grouping_preserves_tensor_and_basis T b count positions
  let p (i : Fin 3) : (Fin N → I i) ≃ (∀ c, Fin (count c) → I i) :=
    { toFun := fun w c r ↦ w (positions.symm ⟨c, r⟩)
      invFun := fun w t ↦ w (positions t).1 (positions t).2
      left_inv := by
        intro w
        funext t
        exact congrArg w (positions.symm_apply_apply t)
      right_inv := by
        intro w
        funext c r
        exact congrArg (fun a : Σ c, Fin (count c) ↦ w a.1 a.2)
          (positions.apply_symm_apply ⟨c, r⟩) }
  obtain ⟨f, hf, hfb, _⟩ := mme_basisAllAllowedSubtensor_basis_equiv_transport
    (T.kronPow N) (TensorObj.kronFin k (fun c ↦ T.kronPow (count c)))
    (fun i ↦ TensorObj.kronPowModeWordBasis T i (b i) N)
    (fun i ↦ TensorObj.kronFinModePiBasis k (fun c ↦ T.kronPow (count c)) i
      (fun c ↦ TensorObj.kronPowModeWordBasis T i (b i) (count c)))
    e p hb ht
    (fun i (w : Fin N → I i) ↦
      ∀ c, allowed c i (fun r ↦ w (positions.symm ⟨c, r⟩)))
    (fun i (w : ∀ c, Fin (count c) → I i) ↦ ∀ c, allowed c i (w c))
    (fun _ _ ↦ Iff.rfl)
  exact ⟨f, hf, hfb⟩


