-- Prove2me | Theorems.Thm_mme_recursive_CW_supported_words_of_joint_histogram
-- name    : mme_recursive_CW_supported_words_of_joint_histogram
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:17:07.085621+00:00
-- url     : https://prove2.me/theorems/0703f3f2-a79a-4e3a-93bb-a0f7d154209c
-- title:
--   Realizing jointly supported complete-word histograms
-- statement:
--   Let $P$ be a finite set of positions, with a cell map $c:P\to C$, prescribed grades $s_i(c)$, and complete-word histograms $\mu_i(c,w)$. Suppose nonnegative integer joint counts $\lambda_c(v_0,v_1,v_2)$ have total mass $|c^{-1}(c)|$ in each cell and marginal counts $\mu_i$. Assume every triple of positive joint count has the prescribed grades and satisfies $v_0(r)+v_1(r)+v_2(r)=2$ at every elementary position $r$.
--
--   Then there exist three word assignments on $P$ with the prescribed grades and marginal histograms, satisfying the same pointwise support equation, whose full joint histogram is exactly $\lambda$. No finiteness assumption on the cell-label type is required.
-- source:
--   Integer cell-word realization with mass and grade constraints; supported-word extraction for literal profiled CW blocks.

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_supported_words

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.ProfiledCW
open scoped Classical

theorem mme_recursive_CW_supported_words_of_joint_histogram
    {P C : Type*} [Fintype P] {ell : ℕ}
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (joint : C → (Fin 3 → CompleteWord ell) → ℕ)
    (hmass : ∀ c, ∑ v, joint c v = Nat.card {p : P // cell p = c})
    (hmarginal : ∀ i c s, ∑ v, (if v i = s then joint c v else 0) = mu i c s)
    (hgrade : ∀ c v, 0 < joint c v → ∀ i, grade (v i) = shape c i)
    (hsupport : ∀ c v, 0 < joint c v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    ∃ w : Fin 3 → P → CompleteWord ell,
      (∀ i p, grade (w i p) = shape (cell p) i) ∧
      (∀ i, Useful cell (mu i) (w i)) ∧
      (∀ p r, (w 0 p r).val + (w 1 p r).val + (w 2 p r).val = 2) ∧
      Useful cell joint (fun p i ↦ w i p) := by sorry
