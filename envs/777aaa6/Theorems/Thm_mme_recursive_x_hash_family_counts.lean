-- Prove2me | Theorems.Thm_mme_recursive_x_hash_family_counts
-- name    : mme_recursive_x_hash_family_counts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-11T22:45:20.332702+00:00
-- url     : https://prove2.me/theorems/9957adcf-e7fe-4a89-94d1-4daee877186e
-- title:
--   Recursive profile families have uniform X-fibers and exact thin-profile reduction
-- statement:
--   Fix a half-grade $h$, parent triples $p^{(r)}\in\mathbb N^3$, word lengths $n_r$, and prescribed integer joint histograms $m_r$. Put
--
--   $$C_r=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p^{(r)}_i\},\qquad W=\prod_r C_r^{n_r}.$$
--
--   Let $T\subseteq W$ contain the words whose joint histogram in each parent component is exactly $m_r$. Let $A\subseteq W$ contain all words whose three coordinate histograms in each component are the marginals of $m_r$. Thus $A$ includes potential competitors with other joint histograms. Write $X(w)$ for the full first-coordinate block and $N_X=|X(A)|$.
--
--   The target family is contained in the ambient family. Every ambient word has the same X-fiber size, expressed without an assumed degree:
--
--   $$T\subseteq A,\qquad |A|=N_X\,|\{b\in A:X(b)=X(a)\}|\quad(a\in A).$$
--
--   If each parent has at least one coordinate at most one, then $A=T$. This last assertion consumes the established recursive thin-split marginal/joint count theorem. Empty families, zero component lengths, and infeasible prescribed histograms are allowed.
--
--   This is a construction step toward the campaign's [cofinal recursive extraction problem](p2m:theorem/e5acea12-c15b-43b8-9abb-57195c8af2f5). For physical recursive parents one also has a parent coordinate sum of $2h$, making the complementary split have coordinate sum $h$. The proof only needs the left split support and therefore remains valid for arbitrary parent bounds. Fine Y/Z compatibility, hole repair, asymptotic profile estimates, and the numerical witness remain outside this result.
-- source:
--   Finite auxiliary formalization of the recursive hashing step in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.2, Claim 6.6 and Lemma 6.7; https://arxiv.org/html/2404.16349v2#S6.SS2. The result isolates the finite counting and X-isolation argument. It does not assert the asymptotic Salem-Spencer set estimate or the full extraction theorem.

import Definitions.Def_mme_recursive_x_hash_families

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
set_option autoImplicit false

theorem mme_recursive_x_hash_family_counts (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ) :
    target (n := n) m ⊆ ambient (n := n) m ∧
    (∀ a ∈ ambient (n := n) m,
      (ambient (n := n) m).card = ((ambient (n := n) m).image (block 0)).card *
        ((ambient (n := n) m).filter (fun b ↦ block 0 b = block 0 a)).card) ∧
    ((∀ r, ∃ i, parent r i ≤ 1) → ambient (n := n) m = target m) := by sorry
