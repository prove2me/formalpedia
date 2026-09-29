-- Prove2me | Theorems.Thm_mme_dwz_table2_first_hash_x_denominator_lower
-- name    : mme_dwz_table2_first_hash_x_denominator_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:52:03.108429+00:00
-- url     : https://prove2.me/theorems/d2c09550-0cc2-42a7-85c9-be013263c8cd
-- title:
--   Entropy lower bound for the Table-2 first-hash X denominator
-- statement:
--   The exact X-word universe in the Table-2 first hashing step is bounded below, division-free, by its entropy exponential with explicit five-cell loss (6(n+1))^5. The theorem also handles m=0.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Section 3.10; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_first_hash_x_denominator_lower (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    Real.exp
        ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (mme_modern_marginal MME.DWZSquare.shapeX
              MME.DWZSquare.alpha)) ≤
      (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5 *
        (Nat.card XWord : ℝ) := by
  sorry
