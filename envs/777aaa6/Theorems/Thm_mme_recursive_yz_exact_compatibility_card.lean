-- Prove2me | Theorems.Thm_mme_recursive_yz_exact_compatibility_card
-- name    : mme_recursive_yz_exact_compatibility_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:16:24.336911+00:00
-- url     : https://prove2.me/theorems/59b18567-8b3d-45ba-bebf-2b3837026c6f
-- title:
--   Recursive Y/Z filtering: exact compatibility count with both halves
-- statement:
--   Fix parent components of total grade $2h$ and a recursive split address with prescribed left-split counts $m_r(a)$. The physical cell $(r,a)$ contains both occurrences whose left split is $a$ and occurrences whose right split is $a$, so it has size $m_r(a)+m_r(\bar a)$.
--
--   Let $W$ be any finite fine-word alphabet (in particular, the full CW child-word alphabet), and prescribe cell histograms $\mu(c,w)$ summing to these physical cell sizes. For any boundary predicate and retained-mode grouping, the exact number of compatible fine words is
--
--   $$\prod_{s\in\mathcal P}\frac{(\sum_w\mu_{\mathcal P}(s,w))!}{\prod_w\mu_{\mathcal P}(s,w)!},$$
--
--   where $\mathcal P$ separates individual boundary cells and merges all remaining cells with the same retained-mode label. On a boundary cell, $\mu_{\mathcal P}=\mu$; on an interior part, it is the sum of the corresponding cell histograms.
--
--   Taking the boundary $k'=0$ and grouping by the Y grade gives the finite counting identity underlying Claim 6.19. Taking the boundary $i'=0$ or $j'=0$ and grouping by the Z grade gives its Z analogue. Both halves are included. The statement is exact at finite size and does not claim the subsequent entropy asymptotics, competitor loss, or tensor extraction.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Claim 6.19 and the counting step for Claim 6.20; https://arxiv.org/html/2404.16349v2#S6.SS5. The arbitrary boundary/group version is a finite generalization of the two applications in the paper.

import Definitions.Def_mme_recursive_yz_physical_words
open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_yz_exact_compatibility_card {half R : ℕ} {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (htype : ∀ r, MME.RecursiveThinSplit.HasJointCounts (a r) (m r))
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2)) :
    Nat.card {f : Position n → W //
        Compatible (fullCell htotal a) boundary group mu f} =
      compatibilityNumber boundary group mu := by sorry
