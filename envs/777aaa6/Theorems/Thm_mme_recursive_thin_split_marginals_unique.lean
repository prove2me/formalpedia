-- Prove2me | Theorems.Thm_mme_recursive_thin_split_marginals_unique
-- name    : mme_recursive_thin_split_marginals_unique
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-11T22:09:51.863143+00:00
-- url     : https://prove2.me/theorems/d5246b2d-20f3-4d60-91a8-6e08a58efd5d
-- title:
--   Recursive splits with a coordinate at most one are determined by their marginals
-- statement:
--   Let $h\in\mathbb N$ and $p=(p_0,p_1,p_2)\in\mathbb N^3$. Define the finite admissible split support
--
--   $$S_h(p)=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p_i\text{ for }i=0,1,2\}.$$
--
--   Assume that $p_i\le1$ for at least one coordinate $i$. For any two real weight functions $\rho,\alpha:S_h(p)\to\mathbb R$, equality of all three coordinate marginals implies
--
--   $$\rho=\alpha.$$
--
--   No positivity, normalization, symmetry, or numerical optimizer assumptions are needed.
--
--   For the fourth-power witness, set $h=4$ and let $p_0+p_1+p_2=8$. The theorem covers the permutations of $(1,1,6)$, $(1,2,5)$, and $(1,3,4)$, as well as boundary components with a zero coordinate. Its intended consumer is the recursive counting/rate part of [the cofinal extraction problem](p2m:theorem/e5acea12-c15b-43b8-9abb-57195c8af2f5). It does not construct independent tensor copies or prove that extraction problem.
-- source:
--   New auxiliary lemma derived from the admissible recursive split support in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6 (Table 3), Proposition 6.3, and Section 6.2, Claim 6.6; https://arxiv.org/html/2404.16349v2#S6. This structural simplification is not asserted as a separately numbered theorem in the paper.

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Tactic.FinCases

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

theorem mme_recursive_thin_split_marginals_unique (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (rho alpha : Split half parent → ℝ)
    (hmarg : ∀ (i : Fin 3) (j : Fin (half + 1)),
      mme_modern_marginal (fun a ↦ a.val i) rho j =
        mme_modern_marginal (fun a ↦ a.val i) alpha j) : rho = alpha := by sorry
