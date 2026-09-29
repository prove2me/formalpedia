-- Prove2me | Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts
-- name    : mme_recursive_thin_split_marginal_joint_counts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-11T22:13:46.810313+00:00
-- url     : https://prove2.me/theorems/b8508c42-8c34-48d0-9357-85665e16623a
-- title:
--   Exact marginal and joint count families coincide on recursive thin split supports
-- statement:
--   Let $h\in\mathbb N$ and $p=(p_0,p_1,p_2)\in\mathbb N^3$. Define the finite admissible split support
--
--   $$S_h(p)=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p_i\text{ for }i=0,1,2\}.$$
--
--   Assume that $p_i\le1$ for at least one coordinate $i$. Let $n\in\mathbb N$ and prescribe arbitrary integer counts $m:S_h(p)\to\mathbb N$. For a word $w\in S_h(p)^n$, let $C_w(a)$ count its occurrences of $a$. Then
--
--   $$\left[\forall i,j,\ \#\{t:w_t(i)=j\}=\sum_{a:a_i=j}m(a)\right]\quad\Longleftrightarrow\quad\left[\forall a,\ C_w(a)=m(a)\right].$$
--
--   Consequently, the two word families have equal cardinality. This includes the empty word and infeasible prescribed counts; no positivity or total-count assumption on the prescribed histogram is required.
--
--   For the fourth-power witness, set $h=4$ and let $p_0+p_1+p_2=8$. The theorem covers the permutations of $(1,1,6)$, $(1,2,5)$, and $(1,3,4)$, as well as boundary components with a zero coordinate. Its intended consumer is the recursive counting/rate part of [the cofinal extraction problem](p2m:theorem/e5acea12-c15b-43b8-9abb-57195c8af2f5). It does not construct independent tensor copies or prove that extraction problem.
-- source:
--   New auxiliary lemma derived from the admissible recursive split support in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6 (Table 3), Proposition 6.3, and Section 6.2, Claim 6.6; https://arxiv.org/html/2404.16349v2#S6. This structural simplification is not asserted as a separately numbered theorem in the paper.

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

theorem mme_recursive_thin_split_marginal_joint_counts (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (n : ℕ) (m : Split half parent → ℕ) :
    (∀ w : Fin n → Split half parent, HasMarginalCounts w m ↔ HasJointCounts w m) ∧
      Nat.card {w : Fin n → Split half parent // HasMarginalCounts w m} =
        Nat.card {w : Fin n → Split half parent // HasJointCounts w m} := by sorry
