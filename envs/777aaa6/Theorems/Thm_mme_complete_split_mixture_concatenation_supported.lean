-- Prove2me | Theorems.Thm_mme_complete_split_mixture_concatenation_supported
-- name    : mme_complete_split_mixture_concatenation_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:30:07.50558+00:00
-- url     : https://prove2.me/theorems/ca6cb59c-7cbb-4d46-938d-c075bbda02d3
-- title:
--   Concatenation mixtures preserve constituent grade support
-- statement:
--   Let $\ell\ge1$ and let $a_r$ be nonnegative weights on a finite set $R$, with $\sum_r a_r=1$. For each $r$, let $p_r,q_r$ be normalized nonnegative complete-word profiles at level $\ell$. Suppose $p_r$ vanishes outside words of grade sum $L_r$, $q_r$ vanishes outside words of grade sum $R_r$, and $L_r+R_r=c$ for a common parent grade $c$.
--
--   There is a normalized nonnegative parent complete profile $\beta$ with the exact concatenation-mixture probability
--   $$
--   \beta(x\circ y)=\sum_r a_r p_r(x)q_r(y),
--   $$
--   and
--   $$
--   \sum_i w_i\ne c\quad\Longrightarrow\quad\beta(w)=0.
--   $$
--   The child grades may vary with the split index. This constructs a profile with the support condition required for a parent constituent; it does not establish a tensor extraction or infer the source's boundary-complement identities from grade support.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, printed p.14 (concatenated joint distributions), Remark6.1 on printed p.29 (complete-profile grade support), and Proposition6.3 on printed p.31 (parent mixtures of split/complementary-split child products). https://arxiv.org/abs/2404.16349v2. This is the finite support-preservation implication, not the source's without-loss-of-generality reduction or recursive extraction theorem.

import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME.CompleteSplit

universe u

set_option autoImplicit false

theorem mme_complete_split_mixture_concatenation_supported {R : Type u} [Fintype R]
    (ell : ℕ) (hell : 1 ≤ ell)
    (weights : R → ℝ) (hw : ∀ r, 0 ≤ weights r)
    (hsumw : ∑ r, weights r = 1) (p q : R → Profile ell)
    (leftGrade rightGrade : R → ℕ) (parentGrade : ℕ)
    (hgrade : ∀ r, leftGrade r + rightGrade r = parentGrade)
    (hp : ∀ r (x : CompleteWord ell),
      (∑ i, (x i).val) ≠ leftGrade r → (p r).probability x = 0)
    (hq : ∀ r (y : CompleteWord ell),
      (∑ i, (y i).val) ≠ rightGrade r → (q r).probability y = 0) :
    ∃ beta : Profile (ell + 1),
      (∀ w, beta.probability w =
        mixedProbability weights
          (fun r ↦ concatenatedProbability hell (p r).probability (q r).probability) w) ∧
      (∀ w : CompleteWord (ell + 1),
        (∑ i, (w i).val) ≠ parentGrade → beta.probability w = 0) := by sorry
