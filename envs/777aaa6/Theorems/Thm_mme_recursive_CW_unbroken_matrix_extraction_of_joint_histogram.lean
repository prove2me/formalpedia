-- Prove2me | Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
-- name    : mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:17:15.735644+00:00
-- url     : https://prove2.me/theorems/36e2a299-aac7-4003-9f42-eff9c353e525
-- title:
--   Intact-block matrix dimensions from integer joint histograms
-- statement:
--   Consider an intact cell-profile block of a power of $\mathrm{CW}_5$ over any field $K$. Let nonnegative integer joint counts $\lambda_c(v_0,v_1,v_2)$ have mass equal to the number of positions in each cell, the prescribed mode marginals, and positive support only on triples with the prescribed grades and $v_0(r)+v_1(r)+v_2(r)=2$ at every elementary position.
--
--   Put
--   $$n_{ij}=\sum_c\sum_v\lambda_c(v)\,|\{r:v_i(r)=v_j(r)=1\}|.$$
--   Then the literal intact block admits the matrix restriction
--   $$\langle5^{n_{02}},5^{n_{01}},5^{n_{12}}\rangle_K\preceq T_{\mathrm{intact}}.$$
--   The result applies at every recursive level. The dimensions are computed directly from the integer joint counts. This extraction uses a single supported assignment and asserts no additional gain from the number of assignments.
-- source:
--   Integer cell-word realization with mass and grade constraints; supported-word extraction for literal profiled CW blocks.

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_supported_words

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.ProfiledCW
open scoped Classical

theorem mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
    {K : Type*} [Field K] {P C : Type} [Fintype P] [Fintype C] {ell L : ℕ}
    (positions : Fin L ≃ P) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (joint : C → (Fin 3 → CompleteWord ell) → ℕ)
    (hmass : ∀ c, ∑ v, joint c v = Nat.card {p : P // cell p = c})
    (hmarginal : ∀ i c s, ∑ v, (if v i = s then joint c v else 0) = mu i c s)
    (hgrade : ∀ c v, 0 < joint c v → ∀ i, grade (v i) = shape c i)
    (hsupport : ∀ c v, 0 < joint c v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun i j ↦ ∑ c, ∑ v, joint c v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v j r).val = 1)).card
    Restrict (MMObj K (5 ^ n 0 2) (5 ^ n 0 1) (5 ^ n 1 2))
      (unbroken K 5 ell L positions cell shape mu) := by sorry
