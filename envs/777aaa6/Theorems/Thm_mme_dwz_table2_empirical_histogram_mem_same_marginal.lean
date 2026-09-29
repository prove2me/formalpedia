-- Prove2me | Theorems.Thm_mme_dwz_table2_empirical_histogram_mem_same_marginal
-- name    : mme_dwz_table2_empirical_histogram_mem_same_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:11:32.712454+00:00
-- url     : https://prove2.me/theorems/38724d60-936f-4c2e-9718-5c671bf058c0
-- title:
--   Table-2 empirical histograms satisfy all three prescribed marginals
-- statement:
--   For every positive integer scale multiplier m, each length-n Table-2 word satisfying the prescribed X-, Y-, and Z-coordinate counts has an empirical joint distribution whose entropy belongs to the exact same-marginal feasible entropy set used in Algorithm 2. Here n is the Table-2 integral scale times m. The conclusion supplies literal set membership; it neither assumes nor asserts that the entropy supremum is attained.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2, Section 3.10, and Equation (21); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_empirical_histogram_mem_same_marginal
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
    ∀ w : MarginalTriple,
      let p : Fin 15 → ℝ := fun s ↦
        (Fintype.card {t : Fin sourceLength // w.1 t = s} : ℝ) /
          (sourceLength : ℝ)
      mme_modern_entropyBits p ∈
        MME.DWZSquare.sameMarginalEntropyValues := by
  sorry
