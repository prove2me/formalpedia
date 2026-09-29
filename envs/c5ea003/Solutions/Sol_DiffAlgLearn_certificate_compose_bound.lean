-- Prove2me | solution 1 for DiffAlgLearn.certificate_compose_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:18:58.668984+00:00
-- url     : https://prove2.me/submissions/8fd42c10-f8f6-48ed-bbeb-4e0f6fe5ab30

import Mathlib
import Definitions.Def_Bridges_PosetTheory_DifferentialAlgebraicLearning

open DiffAlgLearn

theorem solution (c₁ c₂ : FullConvergenceCertificate) :
    (c₁.ritt_length + c₂.ritt_length) * (max c₁.dimension c₂.dimension) ^ 2 *
      (c₁.galois_derived_length * c₂.galois_derived_length) ≥
    c₁.ritt_length * c₁.dimension ^ 2 * c₁.galois_derived_length := by
  have hmax : c₁.dimension ≤ max c₁.dimension c₂.dimension := le_max_left _ _
  have hdim : c₁.dimension ^ 2 ≤ (max c₁.dimension c₂.dimension) ^ 2 :=
    Nat.pow_le_pow_left hmax 2
  have hritt : c₁.ritt_length ≤ c₁.ritt_length + c₂.ritt_length := Nat.le_add_right _ _
  have hgal : c₁.galois_derived_length ≤
      c₁.galois_derived_length * c₂.galois_derived_length := by
    simpa [Nat.mul_one] using
      Nat.mul_le_mul_left c₁.galois_derived_length c₂.galois_pos
  have h1 : c₁.ritt_length * c₁.dimension ^ 2 ≤
      (c₁.ritt_length + c₂.ritt_length) * (max c₁.dimension c₂.dimension) ^ 2 :=
    Nat.mul_le_mul hritt hdim
  have h2 :
      c₁.ritt_length * c₁.dimension ^ 2 * c₁.galois_derived_length ≤
        (c₁.ritt_length + c₂.ritt_length) * (max c₁.dimension c₂.dimension) ^ 2 *
          c₁.galois_derived_length :=
    Nat.mul_le_mul_right _ h1
  have h3 :
      (c₁.ritt_length + c₂.ritt_length) * (max c₁.dimension c₂.dimension) ^ 2 *
          c₁.galois_derived_length ≤
        (c₁.ritt_length + c₂.ritt_length) * (max c₁.dimension c₂.dimension) ^ 2 *
          (c₁.galois_derived_length * c₂.galois_derived_length) :=
    Nat.mul_le_mul_left _ hgal
  exact le_trans h2 h3
