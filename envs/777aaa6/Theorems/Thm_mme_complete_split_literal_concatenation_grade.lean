-- Prove2me | Theorems.Thm_mme_complete_split_literal_concatenation_grade
-- name    : mme_complete_split_literal_concatenation_grade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:22:01.235721+00:00
-- url     : https://prove2.me/theorems/e601f3cc-2779-4b99-8fa1-79f589bc4b80
-- title:
--   Literal complete-word concatenation preserves the sum of fine grades
-- statement:
--   Let $\ell\ge1$ and let $x,y$ be two ordered complete words of length $L=2^{\ell-1}$ over $\{0,1,2\}$. Their parent word $x\circ y$ has length $2L=2^\ell$, evaluates to the first word on the first half and to the second on the second half, and splits back to $(x,y)$. Its grade sum satisfies
--   $$
--   \sum_{i=0}^{2L-1}(x\circ y)_i=\sum_{i=0}^{L-1}x_i+\sum_{i=0}^{L-1}y_i.
--   $$
--   This identifies the actual ordered source words used by recursive complete-split profiles. The exact length cast in Lean only reindexes equal natural lengths; it does not permute the letters.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, printed p.14 (joint distributions on concatenated integer sequences and Definition3.4), and Proposition6.3, printed p.31 (regional full-profile mixtures of concatenation products). https://arxiv.org/abs/2404.16349v2. This is the elementary literal finite-profile layer, not the recursive tensor-extraction theorem.

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false

theorem mme_complete_split_literal_concatenation_grade (ell : ℕ) (hell : 1 ≤ ell) (x y : CompleteWord ell) :
    (∀ i, ((completeWordSplitEquiv ell hell).symm (x, y)) i =
      Fin.addCases x y (Fin.cast (completeWord_length_double ell hell) i)) ∧
    (completeWordSplitEquiv ell hell
      ((completeWordSplitEquiv ell hell).symm (x, y)) = (x, y)) ∧
    (∑ i, (((completeWordSplitEquiv ell hell).symm (x, y)) i).val) =
      (∑ i, (x i).val) + ∑ i, (y i).val := by sorry
