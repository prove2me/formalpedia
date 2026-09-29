-- Prove2me | Theorems.Thm_mme_dwz_table2_scaled_shape_marginals
-- name    : mme_dwz_table2_scaled_shape_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:51:53.008633+00:00
-- url     : https://prove2.me/theorems/851f9adc-b7ee-4cf5-b686-8be3dcf3028c
-- title:
--   Exact normalization of the scaled Table-2 shape marginals
-- statement:
--   For every positive multiplier m, the integral Table-2 X, Y, and Z marginal counts divided by scale*m equal exactly the real shape marginals of the Table-2 distribution alpha.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Section 3.10; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_scaled_shape_marginals (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    (∀ x, (alphaX x : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha x) ∧
    (∀ y, (alphaY y : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeY MME.DWZSquare.alpha y) ∧
    ∀ z, (MME.DWZTable2Counts.alphaZ z * m : ℕ) /
        (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha z := by
  sorry
