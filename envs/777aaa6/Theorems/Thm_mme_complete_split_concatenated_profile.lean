-- Prove2me | Theorems.Thm_mme_complete_split_concatenated_profile
-- name    : mme_complete_split_concatenated_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:21:32.641633+00:00
-- url     : https://prove2.me/theorems/46d5ab24-26e8-4a76-8b9f-7d70e52fba5e
-- title:
--   A product of child full-word profiles is a normalized parent profile
-- statement:
--   Let $\ell\ge1$, and let $p,q$ be nonnegative normalized distributions on the complete words of length $2^{\ell-1}$. There is a nonnegative normalized parent complete-split profile $\beta$ on words of length $2^\ell$ such that
--   $$
--   \beta(x\circ y)=p(x)q(y),\qquad
--   \sum_y\beta(x\circ y)=p(x),\qquad
--   \sum_x\beta(x\circ y)=q(y).
--   $$
--   The parent probability is exactly the literal concatenation-product function on every parent word. This supplies complete-word consistency data for recursive interfaces. It does not establish empirical realizability, tensor extraction, or intersection of independently frequent asymptotic witnesses.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, printed p.14 (joint distributions on concatenated integer sequences and Definition3.4), and Proposition6.3, printed p.31 (regional full-profile mixtures of concatenation products). https://arxiv.org/abs/2404.16349v2. This is the elementary literal finite-profile layer, not the recursive tensor-extraction theorem.

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false

theorem mme_complete_split_concatenated_profile (ell : ℕ) (hell : 1 ≤ ell) (p q : Profile ell) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        concatenatedProbability hell p.probability q.probability w) ∧
      (∀ x y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        p.probability x * q.probability y) ∧
      (∀ x, ∑ y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        p.probability x) ∧
      (∀ y, ∑ x, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        q.probability y) := by sorry
