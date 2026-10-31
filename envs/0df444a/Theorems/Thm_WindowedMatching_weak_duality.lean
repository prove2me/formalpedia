-- Prove2me | Theorems.Thm_WindowedMatching_weak_duality
-- name    : WindowedMatching.weak_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:23.292275+00:00
-- url     : https://prove2.me/theorems/edfad9cf-179b-4177-a199-8d1ca4e7cea9
-- title:
--   Weak duality: $\mathrm{OFF}\le\sum_k\lambda_k$ for feasible $\lambda$
-- statement:
--   Let $G$ be a finite simple graph with edge weights $w$, and let $\lambda$ be a non-negative function on its vertices with
--   $$w_{(a,b)}\le\lambda_a+\lambda_b$$
--   for every edge $(a,b)$. Then the maximum weight of a matching of $G$ is at most $\sum_a\lambda_a$.
--
--   The paper uses this for $G=G_{d,\sigma}$ and $\lambda_k=p^f(s_k)+q(b_k)$, which gives $\mathrm{OFF}\le\sum_kp^f(s_k)+q(b_k)$.
--
--   Differences from the source:
--   - generalization: OFF $\le\sum_kp^f(s_k)+q(b_k)$ on $G_{d,\sigma}$ → every finite simple graph, every weight and every feasible $\lambda$; reason: the page's claim is the case $G=G_{d,\sigma}$, $\lambda_k=p^f(s_k)+q(b_k)$, using `dual_feasible`
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.7, "We can conclude that OFF ≤ Σ_k pf(sk) + q(bk)"

import Definitions.Def_ProphetMatchingEFGT_MatchingModel

namespace WindowedMatching

/-- Weak duality for (Offline Dual): if `λ ≥ 0` and `w_e ≤ λ_a + λ_b` on every edge `e = (a, b)`, then
the maximum weight of a matching is at most `Σ_a λ_a` (arXiv:1808.03526v1, §3.2, proof of
Theorem 3.3, p.7, "OFF ≤ Σ_k p^f(s_k) + q(b_k)").

**Formalization Note.** Stated for every finite simple graph, every weight and every feasible `λ`.
The paper applies it to `G_{d,σ}` and `λ_k = p^f(s_k) + q(b_k)`. -/
theorem weak_duality {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : ProphetMatchingEFGT.Edge G → ℝ) (lam : V → ℝ)
    (hlam : ∀ a, 0 ≤ lam a)
    (hfeas : ∀ (a b : V) (hab : G.Adj a b), w ⟨s(a, b), hab⟩ ≤ lam a + lam b) :
    ProphetMatchingEFGT.optWeight G w ≤ ∑ a, lam a := by sorry

end WindowedMatching
