-- Prove2me | Theorems.Thm_mme_recursive_thin_split_entropy_penalty_zero
-- name    : mme_recursive_thin_split_entropy_penalty_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-11T22:13:31.717045+00:00
-- url     : https://prove2.me/theorems/ac19fa40-3191-46fc-b2ad-36c3713c5533
-- title:
--   The recursive entropy penalty is exactly zero on thin split supports
-- statement:
--   Let $h\in\mathbb N$ and $p=(p_0,p_1,p_2)\in\mathbb N^3$. Define the finite admissible split support
--
--   $$S_h(p)=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p_i\text{ for }i=0,1,2\}.$$
--
--   Assume that $p_i\le1$ for at least one coordinate $i$. Let $\alpha$ be a nonnegative probability distribution on $S_h(p)$, and let $D(\alpha)$ be the set of nonnegative probability distributions on this support with the same three coordinate marginals. Then
--
--   $$D(\alpha)=\{\alpha\},\qquad \forall\rho\in D(\alpha),\ H_{\mathrm{nat}}(\rho)=H_{\mathrm{nat}}(\alpha),\qquad P_\alpha=0,$$
--
--   where $H_{\mathrm{nat}}(\rho)=-\sum_a\rho(a)\log\rho(a)$ and $P_\alpha=\sup_{\rho\in D(\alpha)}H_2(\rho)-H_2(\alpha)$ is the penalty in bits. Zero probabilities are allowed. The supremum is attained at $\alpha$.
--
--   For the fourth-power witness, set $h=4$ and let $p_0+p_1+p_2=8$. The theorem covers the permutations of $(1,1,6)$, $(1,2,5)$, and $(1,3,4)$, as well as boundary components with a zero coordinate. Its intended consumer is the recursive counting/rate part of [the cofinal extraction problem](p2m:theorem/e5acea12-c15b-43b8-9abb-57195c8af2f5). It does not construct independent tensor copies or prove that extraction problem.
-- source:
--   New auxiliary lemma derived from the admissible recursive split support in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6 (Table 3), Proposition 6.3, and Section 6.2, Claim 6.6; https://arxiv.org/html/2404.16349v2#S6. This structural simplification is not asserted as a separately numbered theorem in the paper.

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

theorem mme_recursive_thin_split_entropy_penalty_zero (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (alpha : Split half parent → ℝ)
    (hnonneg : ∀ a, 0 ≤ alpha a) (hsum : ∑ a, alpha a = 1) :
    SameMarginalDistributions alpha = {alpha} ∧
      (∀ rho ∈ SameMarginalDistributions alpha,
        (∑ a, Real.negMulLog (rho a)) = ∑ a, Real.negMulLog (alpha a)) ∧
      entropyPenalty alpha = 0 := by sorry
