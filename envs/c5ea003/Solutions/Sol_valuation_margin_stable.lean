-- Prove2me | solution 1 for valuation_margin_stable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:27:58.702014+00:00
-- url     : https://prove2.me/submissions/8e37587c-795a-49f6-b88d-020b6f47653f

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




/-! ## §4. Ultrametric Row Bound -/



/-! ## §5. Structures -/




/-! ## §6. Evaluation -/





/-! ## §7. Bias Cancellation and Affine Lipschitz -/



/-! ## §8. Activation Lipschitz -/



/-! ## §9. Layered Map Lipschitz -/


/-! ## §10. Network Composition -/







/-! ## §11. Margin Definitions -/











/-! ## §12. Margin and Radius Theorems -/






theorem competitorMargin_le_gap [DecidableEq ι]
    (y : ι → K) (good j : ι) (hj : j ≠ good)
    (hne : (Finset.univ.erase good).Nonempty) :
    competitorMargin y good hne ≤ ‖y good - y j‖ :=
  Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)





/-! ## §13. Margin Perturbation -/

theorem network_coord_perturbation [Nonempty ι]
    (f : (ι → K) → (ι → K)) (L : ℝ)
    (hLip : ∀ x y, vecSupDist (f x) (f y) ≤ L * vecSupDist x y)
    (x z : ι → K) (j : ι) :
    ‖f z j - f x j‖ ≤ L * vecSupDist z x :=
  le_trans (vecSupDist_coord_le (f z) (f x) j) (hLip z x)


/-! ## §14. The Headline Certification Theorem -/


/-! ## §15. Additional Theorems -/












theorem solution[DecidableEq ι] [Nonempty ι]
    (f : (ι → K) → (ι → K)) (L : ℝ)
    (hLip : ∀ x y, vecSupDist (f x) (f y) ≤ L * vecSupDist x y)
    (x z : ι → K) (good : ι)
    (hL : 0 < L)
    (hne : (Finset.univ.erase good).Nonempty)
    (hMargin : 0 < competitorMargin (f x) good hne)
    (hclose : vecSupDist z x < competitorMargin (f x) good hne / (2 * L)) :
    ∀ j, j ≠ good → ‖f z good - f z j‖ > 0 := by
  intro j hj
  have hgap : competitorMargin (f x) good hne ≤ ‖f x good - f x j‖ :=
    competitorMargin_le_gap (f x) good j hj hne
  have hpert_good : ‖f z good - f x good‖ ≤ L * vecSupDist z x :=
    network_coord_perturbation f L hLip x z good
  have hpert_j : ‖f z j - f x j‖ ≤ L * vecSupDist z x :=
    network_coord_perturbation f L hLip x z j
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero : ‖f z good - f z j‖ = 0 :=
    le_antisymm h_not_pos (norm_nonneg _)
  have h_eq : f z good = f z j := by rwa [norm_eq_zero, sub_eq_zero] at h_zero
  have key : ‖f x good - f x j‖ ≤ L * vecSupDist z x := by
    have rw_eq : f x good - f x j = -(f z good - f x good) + (f z j - f x j) := by
      rw [h_eq]; ring
    rw [rw_eq]
    calc ‖-(f z good - f x good) + (f z j - f x j)‖
        ≤ max ‖-(f z good - f x good)‖ ‖f z j - f x j‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖f z good - f x good‖ ‖f z j - f x j‖ := by rw [norm_neg]
      _ ≤ max (L * vecSupDist z x) (L * vecSupDist z x) :=
          max_le_max hpert_good hpert_j
      _ = L * vecSupDist z x := max_self _
  have bound : competitorMargin (f x) good hne ≤ L * vecSupDist z x :=
    le_trans hgap key
  have small : L * vecSupDist z x < L * (competitorMargin (f x) good hne / (2 * L)) :=
    mul_lt_mul_of_pos_left hclose hL
  have half : L * (competitorMargin (f x) good hne / (2 * L)) =
      competitorMargin (f x) good hne / 2 := by field_simp
  linarith
