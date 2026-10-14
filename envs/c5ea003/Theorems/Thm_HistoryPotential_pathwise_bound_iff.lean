-- Prove2me | Theorems.Thm_HistoryPotential_pathwise_bound_iff
-- name    : HistoryPotential.pathwise_bound_iff
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:09:41.168632+00:00
-- url     : https://prove2.me/theorems/74a1c295-c688-47b7-9722-534b73d656ad
-- title:
--   A consistent history potential from bounds on every finite path
-- statement:
--   Let $M$ be a request alphabet, let $I$ be a nonempty index set, and let $W(l,i)$ and $B(l)$ be real-valued functions of finite histories (and, for $W$, an index). The following assertions are equivalent.
--
--   There is a real-valued potential on histories with
--   $$
--   \Phi(\varnothing)=0,\qquad \Phi(l)\le B(l),\qquad
--   W(lr,i)-W(l,i)\le\Phi(lr)-\Phi(l)
--   $$
--   for every history $l$, request $r$, and index $i$.
--
--   For every request sequence $\sigma$ of length $m$ there are real numbers $u_0,\ldots,u_{m-1}$ such that
--   $$
--   W(\sigma_{\le t+1},i)-W(\sigma_{\le t},i)\le u_t
--   \quad(t<m,\ i\in I),\qquad
--   \sum_{t<m}u_t\le B(\sigma).
--   $$
--
--   This implication makes separately chosen bounds on each complete sequence consistent on shared prefixes. No finiteness of the alphabet or index set, monotonicity of $W$, or attainment of suprema is assumed. The statement is an elementary abstraction of accumulated extended cost and the telescoping potential criterion, rather than a new competitive bound for k-server.
-- source:
--   Elementary abstraction and converse construction for the accumulated extended cost and potential criterion in E. Koutsoupias, The k-server problem (2009), https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf, Section 3.4, Lemma 2, equation (6), preprint p. 12; potential method pp. 13-15, including Theorems 2-3 and the k+1 and k+2 point cases. K. Brilliantov, E. Bamas, E. Abbe, k-server-bench, https://arxiv.org/html/2604.07240v1, Appendix B.1 Definition 2 and B.2 Theorem 1.

import Mathlib

theorem HistoryPotential.pathwise_bound_iff (M I : Type) [Nonempty I]
    (W : List M → I → ℝ) (B : List M → ℝ) :
    (∃ Φ : List M → ℝ, Φ [] = 0 ∧
      (∀ σ : List M, Φ σ ≤ B σ) ∧
      (∀ (l : List M) (r : M) (i : I),
        W (l ++ [r]) i - W l i ≤ Φ (l ++ [r]) - Φ l)) ↔
    (∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ i : I,
        W (σ.take (t + 1)) i ≤ W (σ.take t) i + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ B σ) := by sorry
