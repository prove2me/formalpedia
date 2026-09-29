-- Prove2me | Theorems.Thm_mme_dwz_table2_same_marginal_triple_count_upper_positive
-- name    : mme_dwz_table2_same_marginal_triple_count_upper_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:21:03.068429+00:00
-- url     : https://prove2.me/theorems/0fc8ae82-443c-4d54-930f-82e71eb1fe5c
-- title:
--   Positive-scale Table-2 three-marginal word count
-- statement:
--   For every positive Table-2 scale multiplier m, the number of length-n words whose X-, Y-, and Z-coordinate counts equal the prescribed Table-2 marginals is at most (n+1)^15 times the exponential of n log(2) times the same-marginal entropy supremum. The polynomial factor counts the possible fifteen-cell joint histograms explicitly.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2, Section 3.10, Equation (21), and Equation (25); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_same_marginal_triple_count_upper_positive
    (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    (Nat.card MarginalTriple : ℝ) ≤
      (((sourceLength + 1 : ℕ) : ℝ)) ^ 15 *
        Real.exp
          ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
            MME.DWZSquare.maxSameMarginalEntropy) := by
  sorry
