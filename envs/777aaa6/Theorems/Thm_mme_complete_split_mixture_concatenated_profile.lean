-- Prove2me | Theorems.Thm_mme_complete_split_mixture_concatenated_profile
-- name    : mme_complete_split_mixture_concatenated_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:22:01.494719+00:00
-- url     : https://prove2.me/theorems/78e9e41f-af06-480c-9dae-a6621a0e3a83
-- title:
--   Normalized mixtures of child concatenation products preserve exact full-word marginals
-- statement:
--   Let $\ell\ge1$ and let $R$ be a finite index set. Suppose $a_r\ge0$, $\sum_r a_r=1$, and $p_r,q_r$ are nonnegative normalized distributions on complete words of length $2^{\ell-1}$. There is a nonnegative normalized parent complete-split profile $\beta$ whose probability on every parent word is the finite mixture of the literal child concatenation products. In particular,
--   $$
--   \beta(x\circ y)=\sum_r a_r p_r(x)q_r(y),\qquad
--   \sum_y\beta(x\circ y)=\sum_r a_r p_r(x),\qquad
--   \sum_x\beta(x\circ y)=\sum_r a_r q_r(y).
--   $$
--   This is a mixture of products, not a product of averaged marginals: dependence on the common index $r$ is retained. Zero weights and zero probabilities are allowed without division. This finite construction supplies the exact full-profile mixture equations used in recursive interfaces, but does not prove tensor extraction or the numerical feasibility of a prescribed parent profile.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, printed p.14 (joint distributions on concatenated integer sequences and Definition3.4), and Proposition6.3, printed p.31 (regional full-profile mixtures of concatenation products). https://arxiv.org/abs/2404.16349v2. This is the elementary literal finite-profile layer, not the recursive tensor-extraction theorem.

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false

theorem mme_complete_split_mixture_concatenated_profile {R : Type u} [Fintype R]
    (ell : ℕ) (hell : 1 ≤ ell)
    (weights : R → ℝ) (hw : ∀ r, 0 ≤ weights r)
    (hsumw : ∑ r, weights r = 1) (p q : R → Profile ell) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        mixedProbability weights
          (fun r ↦ concatenatedProbability hell (p r).probability (q r).probability) w) ∧
      (∀ x y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * ((p r).probability x * (q r).probability y)) ∧
      (∀ x, ∑ y, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * (p r).probability x) ∧
      (∀ y, ∑ x, beta.probability ((completeWordSplitEquiv ell hell).symm (x, y)) =
        ∑ r, weights r * (q r).probability y) := by sorry
