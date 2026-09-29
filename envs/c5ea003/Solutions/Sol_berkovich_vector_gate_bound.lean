-- Prove2me | solution 1 for berkovich_vector_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:01:31.181642+00:00
-- url     : https://prove2.me/submissions/55b8114d-9272-4295-9d89-a52e4a9493b6

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

theorem vecSupNorm_nonneg [Nonempty ι] (x : ι → K) : 0 ≤ vecSupNorm x :=
  le_trans (norm_nonneg _) (vecSupNorm_coord_le x (Classical.arbitrary ι))








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





/-! ## §7. Bias Cancellation and Affine Lipschitz -/



/-! ## §8. Activation Lipschitz -/



/-! ## §9. Layered Map Lipschitz -/


/-! ## §10. Network Composition -/







/-! ## §11. Margin Definitions -/











/-! ## §12. Margin and Radius Theorems -/











/-! ## §13. Margin Perturbation -/



/-! ## §14. The Headline Certification Theorem -/


/-! ## §15. Additional Theorems -/












theorem solution[Nonempty ι] [Nonempty κ]
    (L : PadicAffineVecLayer K ι κ) (x : ι → K) :
    vecSupNorm (evalAffineVec L x) ≤
      opSupNorm L.weight * vecSupNorm x +
      Finset.univ.sup' Finset.univ_nonempty (fun j => ‖L.bias j‖) := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro j _
  show ‖evalAffineVec L x j‖ ≤ _
  simp only [evalAffineVec]
  calc ‖(∑ i, L.weight j i * x i) + L.bias j‖
      ≤ max ‖∑ i, L.weight j i * x i‖ ‖L.bias j‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max (opSupNorm L.weight * vecSupNorm x)
          (Finset.univ.sup' Finset.univ_nonempty (fun j => ‖L.bias j‖)) :=
        max_le_max (ultrametric_row_bound _ _ _)
          (Finset.le_sup' (fun j => ‖L.bias j‖) (Finset.mem_univ j))
    _ ≤ opSupNorm L.weight * vecSupNorm x +
          Finset.univ.sup' Finset.univ_nonempty (fun j => ‖L.bias j‖) :=
        max_le (le_add_of_nonneg_right (le_trans (norm_nonneg _)
          (Finset.le_sup' (fun j => ‖L.bias j‖)
            (Finset.mem_univ (Classical.arbitrary κ)))))
          (le_add_of_nonneg_left (mul_nonneg (opSupNorm_nonneg _) (vecSupNorm_nonneg _)))
