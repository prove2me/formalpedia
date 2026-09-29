-- Prove2me | Theorems.Thm_mme_recursive_x_hash_finite_isolation
-- name    : mme_recursive_x_hash_finite_isolation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-11T22:45:15.123062+00:00
-- url     : https://prove2.me/theorems/85f4e322-8471-4983-8140-c2b8d9e97bc5
-- title:
--   Finite recursive X-isolation from actual profile counts
-- statement:
--   Fix a half-grade $h$, parent triples $p^{(r)}\in\mathbb N^3$, word lengths $n_r$, and prescribed integer joint histograms $m_r$. Put
--
--   $$C_r=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p^{(r)}_i\},\qquad W=\prod_r C_r^{n_r}.$$
--
--   Let $T\subseteq W$ contain the words whose joint histogram in each parent component is exactly $m_r$. Let $A\subseteq W$ contain all words whose three coordinate histograms in each component are the marginals of $m_r$. Thus $A$ includes potential competitors with other joint histograms. Write $X(w)$ for the full first-coordinate block and $N_X=|X(A)|$.
--
--   Suppose the total number of positions is $N+1>0$, with any fixed enumeration of the positions by $\{0,\ldots,N\}$. Let $p>h$ be an odd prime, and let $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$ be three-term-progression-free. Assume the explicit family-count bound
--
--   $$8|A|\le pN_X.$$
--
--   Use the actual affine hashes, with weights $w_t$ and offsets $b_0,w_0$ in $\mathbb F_p$:
--
--   $$h_X(I)=b_0+\sum_t I_tw_t,\quad h_Y(J)=b_0+w_0+\sum_tJ_tw_t,\quad h_Z(K)=b_0+\tfrac12\left(w_0+\sum_t(h-K_t)w_t\right).$$
--
--   For a hash state $q$, let $E_q\subseteq A$ be the family obtained by independently requiring each of these three hashes to belong to the embedded set $S$. There are a hash state $q$ and a family $I\subseteq T\cap E_q$ such that
--
--   $$\forall a\in I\ \forall b\in E_q,\quad X(a)=X(b)\Longrightarrow a=b,\qquad |I|\ge\frac{3|T||S|}{4p^2}.$$
--
--   Isolation is relative to the entire retained ambient family, not merely to the selected targets. It requires uniqueness only in X; it imposes no Y- or Z-isolation condition. The collision bound is derived from the actual family counts by the preceding regularity theorem and the existing exact affine hash fiber theorems.
--
--   This is a construction step toward the campaign's [cofinal recursive extraction problem](p2m:theorem/e5acea12-c15b-43b8-9abb-57195c8af2f5). For physical recursive parents one also has a parent coordinate sum of $2h$, making the complementary split have coordinate sum $h$. The proof only needs the left split support and therefore remains valid for arbitrary parent bounds. Fine Y/Z compatibility, hole repair, asymptotic profile estimates, and the numerical witness remain outside this result.
-- source:
--   Finite auxiliary formalization of the recursive hashing step in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.2, Claim 6.6 and Lemma 6.7; https://arxiv.org/html/2404.16349v2#S6.SS2. The result isolates the finite counting and X-isolation argument. It does not assert the asymptotic Salem-Spencer set estimate or the full extraction theorem.

import Definitions.Def_mme_recursive_x_hash_families

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
set_option autoImplicit false

theorem mme_recursive_x_hash_finite_isolation (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    {N p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hgrade : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) (hSfree : ThreeAPFree (S : Set ℕ))
    (hbudget : 8 * (ambient (n := n) m).card ≤
      p * ((ambient (n := n) m).image (block 0)).card) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
      I ⊆ target m ∧
      I ⊆ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
      (∀ a ∈ I, ∀ b ∈ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q,
        block 0 a = block 0 b → a = b) ∧
      3 * ((target (n := n) m).card : ℝ) * S.card / (4 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by sorry
