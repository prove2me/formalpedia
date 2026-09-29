-- Prove2me | Theorems.Thm_mme_more_asymmetry_boundary_word_to_complementary_splits
-- name    : mme_more_asymmetry_boundary_word_to_complementary_splits
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T18:39:18.675987+00:00
-- url     : https://prove2.me/theorems/eb061143-e8f5-4025-bc65-b65216eac0a4
-- title:
--   Boundary complete words give complementary admissible splits
-- statement:
--   Let a parent grade be $(0,j,k)$ with $j+k=8$, and let $w=(w_0,w_1,w_2,w_3)$ be a complete four-letter split word whose total Y grade is $j$. The first two letters determine the left child grade $(0,w_0+w_1,4-w_0-w_1)$. The remaining two letters determine the complementary right child grade $(0,w_2+w_3,4-w_2-w_3)$. Both are admissible values of the project's dependent `RecursiveThinSplit.Split` type, including the coordinatewise bounds by the parent. This is the word-to-physical-split map used before summing the released boundary-word multiplicities into the two halves counted by `Stage.mass`.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definition 3.4, Remark 5.2, Proposition 6.3; https://arxiv.org/abs/2404.16349v2. Formal split semantics: pinned Definitions.Def_mme_recursive_thin_split_data and Definitions.Def_mme_recursive_yz_physical_words, Mathlib revision 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e.

import Definitions.Def_mme_recursive_yz_physical_words

set_option autoImplicit false

theorem mme_more_asymmetry_boundary_word_to_complementary_splits (p : Fin 3 → ℕ)
    (hp0 : p 0 = 0)
    (htotal : p 0 + p 1 + p 2 = 2 * 4)
    (w : MME.CompleteSplit.CompleteWord 3)
    (hw : (w 0).val + (w 1).val + (w 2).val + (w 3).val = p 1) :
    ∃ sL : MME.RecursiveThinSplit.Split 4 p,
      (sL.val 0).val = 0 ∧
      (sL.val 1).val = (w 0).val + (w 1).val ∧
      (sL.val 2).val = 4 - ((w 0).val + (w 1).val) ∧
      ((MME.RecursiveYZ.complement htotal sL).val 0).val = 0 ∧
      ((MME.RecursiveYZ.complement htotal sL).val 1).val = (w 2).val + (w 3).val ∧
      ((MME.RecursiveYZ.complement htotal sL).val 2).val = 4 - ((w 2).val + (w 3).val) := by sorry
