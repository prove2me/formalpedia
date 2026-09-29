-- Prove2me | solution 1 for networkLip_fold_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:20:00.136075+00:00
-- url     : https://prove2.me/submissions/39d18fc3-37c6-4aa9-93d0-0aeae9f38547

-- Sol generated from Bridges/UltrametricVectorCertification.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricVectorCertification
/-
# Vector-Valued Ultrametric Neural Network Certification
# via Width-Free Operator Lipschitz Calculus

This file formalizes a complete certified robustness theory for layered
affine-activation networks acting on finite coordinate spaces over a
nonarchimedean normed field, endowed with the sup norm.

## Central Achievement

The headline theorem `ultrametric_lipschitz_certified_robustness` proves that
the certified radius for label stability depends only on multiplicative
layer Lipschitz constants and the output valuation margin — NOT on hidden
widths. This is the ultrametric width-free certification paradigm.

## Structures (10+ novel types)

- `PadicAffineVecLayer` — affine layer with weight kernel and bias
- `UltrametricActivation` — activation with scalar Lipschitz certificate
- `PadicLayeredVecMap` — one affine-activation block
- `UltrametricCertifiedClassifier` — full classification pipeline
- `SupBall` — sup-norm ball as a set
- `ArgmaxSeparated` — predicate for label separation
- `LabelStableOnBall` — robustness predicate

## Bridges

- **Nonarchimedean Analysis ↔ ML**: sup-norm Lipschitz → certified robustness
- **Valuation Geometry ↔ Cryptography**: margin as valuation barrier → noise budget
- **Operator Calculus ↔ Quantum Stability**: width-free bounds → certificates
-/


open Finset

set_option linter.unusedSectionVars false
noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-! ## §1. Vector Sup Norm and Distance -/




/-! ## §2. Basic Properties -/

theorem vecSupNorm_coord_le [Nonempty ι] (x : ι → K) (i : ι) :
    ‖x i‖ ≤ vecSupNorm x :=
  Finset.le_sup' (fun i => ‖x i‖) (Finset.mem_univ i)


theorem vecSupDist_coord_le [Nonempty ι] (x y : ι → K) (i : ι) :
    ‖x i - y i‖ ≤ vecSupDist x y :=
  vecSupNorm_coord_le (fun i => x i - y i) i







/-! ## §3. Operator Sup Norm -/

theorem opSupNorm_entry_le [Nonempty ι] [Nonempty κ] (A : κ → ι → K) (j : κ) (i : ι) :
    ‖A j i‖ ≤ opSupNorm A := by
  calc ‖A j i‖
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => ‖A j i‖) :=
        Finset.le_sup' (fun i => ‖A j i‖) (Finset.mem_univ i)
    _ ≤ opSupNorm A :=
        Finset.le_sup' (fun j => Finset.univ.sup' Finset.univ_nonempty
          (fun i => ‖A j i‖)) (Finset.mem_univ j)

theorem opSupNorm_nonneg [Nonempty ι] [Nonempty κ] (A : κ → ι → K) : 0 ≤ opSupNorm A :=
  le_trans (norm_nonneg _)
    (opSupNorm_entry_le A (Classical.arbitrary κ) (Classical.arbitrary ι))


/-! ## §4. Ultrametric Row Bound -/

/-- **Ultrametric row bound**: ‖∑ᵢ A_ji · xᵢ‖ ≤ opSupNorm A · vecSupNorm x.
    Width-free: no factor of |ι|. -/
theorem ultrametric_row_bound [Nonempty ι] [Nonempty κ]
    (A : κ → ι → K) (x : ι → K) (j : κ) :
    ‖∑ i : ι, A j i * x i‖ ≤ opSupNorm A * vecSupNorm x := by
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty Finset.univ_nonempty
  intro i _
  calc ‖A j i * x i‖ = ‖A j i‖ * ‖x i‖ := norm_mul _ _
    _ ≤ opSupNorm A * vecSupNorm x :=
        mul_le_mul (opSupNorm_entry_le A j i) (vecSupNorm_coord_le x i)
          (norm_nonneg _) (opSupNorm_nonneg A)


/-! ## §5. Structures -/




/-! ## §6. Evaluation -/




theorem layerLip_nonneg [Nonempty ι] [Nonempty κ] (L : PadicLayeredVecMap K ι κ) :
    0 ≤ layerLip L :=
  mul_nonneg L.act.lip_nonneg (opSupNorm_nonneg _)

/-! ## §7. Bias Cancellation and Affine Lipschitz -/

theorem evalAffineVec_sub [Nonempty ι] [Nonempty κ]
    (L : PadicAffineVecLayer K ι κ) (x y : ι → K) (j : κ) :
    evalAffineVec L x j - evalAffineVec L y j =
      ∑ i, L.weight j i * (x i - y i) := by
  simp only [evalAffineVec, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  congr 1; ext i; ring

/-- **Affine sup-Lipschitz**: bias cancels. -/
theorem affine_sup_lipschitz [Nonempty ι] [Nonempty κ]
    (L : PadicAffineVecLayer K ι κ) :
    ∀ x y, vecSupDist (evalAffineVec L x) (evalAffineVec L y)
      ≤ opSupNorm L.weight * vecSupDist x y := by
  intro x y
  apply Finset.sup'_le Finset.univ_nonempty
  intro j _
  show ‖evalAffineVec L x j - evalAffineVec L y j‖ ≤ _
  rw [evalAffineVec_sub L x y j]
  exact ultrametric_row_bound L.weight (fun i => x i - y i) j

/-! ## §8. Activation Lipschitz -/

theorem activation_sup_lipschitz [Nonempty ι]
    (φ : UltrametricActivation K) :
    ∀ x y : ι → K, vecSupDist (fun i => φ.toFun (x i)) (fun i => φ.toFun (y i))
      ≤ φ.lipConst * vecSupDist x y := by
  intro x y
  apply Finset.sup'_le Finset.univ_nonempty
  intro i _
  show ‖φ.toFun (x i) - φ.toFun (y i)‖ ≤ _
  calc ‖φ.toFun (x i) - φ.toFun (y i)‖
      ≤ φ.lipConst * ‖x i - y i‖ := φ.ultra_lipschitz _ _
    _ ≤ φ.lipConst * vecSupDist x y :=
        mul_le_mul_of_nonneg_left (vecSupDist_coord_le x y i) φ.lip_nonneg


/-! ## §9. Layered Map Lipschitz -/

theorem layeredVec_lipschitz_bound [Nonempty ι] [Nonempty κ]
    (L : PadicLayeredVecMap K ι κ) :
    ∀ x y, vecSupDist (evalVec L x) (evalVec L y)
      ≤ layerLip L * vecSupDist x y := by
  intro x y
  show vecSupDist (fun j => L.act.toFun (evalAffineVec L.layer x j))
      (fun j => L.act.toFun (evalAffineVec L.layer y j)) ≤ _
  calc vecSupDist (fun j => L.act.toFun (evalAffineVec L.layer x j))
          (fun j => L.act.toFun (evalAffineVec L.layer y j))
      ≤ L.act.lipConst * vecSupDist (evalAffineVec L.layer x) (evalAffineVec L.layer y) :=
        activation_sup_lipschitz L.act _ _
    _ ≤ L.act.lipConst * (opSupNorm L.layer.weight * vecSupDist x y) :=
        mul_le_mul_of_nonneg_left (affine_sup_lipschitz L.layer x y) L.act.lip_nonneg
    _ = layerLip L * vecSupDist x y := by unfold layerLip; ring

/-! ## §10. Network Composition -/



theorem networkLip_nonneg [Nonempty ι] (net : List (PadicLayeredVecMap K ι ι)) :
    0 ≤ networkLip net := by
  induction net with
  | nil => simp [networkLip]
  | cons L t ih => exact mul_nonneg (layerLip_nonneg L) ih




/-! ## §11. Margin Definitions -/











/-! ## §12. Margin and Radius Theorems -/











/-! ## §13. Margin Perturbation -/



/-! ## §14. The Headline Certification Theorem -/


/-! ## §15. Additional Theorems -/












theorem solution[Nonempty ι]
    (net : List (PadicLayeredVecMap K ι ι)) :
    ∀ x y, vecSupDist (evalNetwork net x) (evalNetwork net y)
      ≤ networkLip net * vecSupDist x y := by
  induction net with
  | nil =>
    intro x y
    simp [evalNetwork, networkLip, id, one_mul]
  | cons L t ih =>
    intro x y
    simp only [evalNetwork, networkLip]
    calc vecSupDist (evalNetwork t (evalVec L x)) (evalNetwork t (evalVec L y))
        ≤ networkLip t * vecSupDist (evalVec L x) (evalVec L y) := ih _ _
      _ ≤ networkLip t * (layerLip L * vecSupDist x y) :=
          mul_le_mul_of_nonneg_left (layeredVec_lipschitz_bound L x y) (networkLip_nonneg t)
      _ = (layerLip L * networkLip t) * vecSupDist x y := by ring
