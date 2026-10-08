-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_area_lemma
-- name    : ZhengQR.CostBounds.area_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:00:07.422358+00:00
-- url     : https://prove2.me/theorems/aa2fa7f6-a662-4a9a-abc7-719fa23cf68e
-- title:
--   Lemma 6: A is increasing and convex; Q = Q* iff A(Q) = λK; Q* increases and r* decreases in K
-- statement:
--   In the stochastic $(Q,r)$ model, let $A(Q)=QH(Q)-\int_0^Q H(y)\,dy$ (Eq. (9)).
--
--   1. $A$ is strictly increasing and convex on $[0,\infty)$.
--   2. For every fixed cost $K'>0$ there is exactly one optimal order quantity.
--   3. For $Q>0$, $Q$ is the optimal order quantity if and only if
--   $$A(Q)=\lambda K.\qquad(10)$$
--   4. If $0<K_1<K_2$ and $Q_1$, $Q_2$ are the optimal order quantities for fixed costs $K_1$, $K_2$, then $Q_1<Q_2$ and $r(Q_2)<r(Q_1)$: the optimal order quantity increases and the optimal reorder point $r^*=r(Q^*)$ decreases in $K$.
--
--   Part 2 is what makes statements about "the optimal order quantity $Q^*$" non-vacuous; part 3 is the equation used to compare $Q^*$ with the EOQ quantity.
--
--   **Formalization Note** The paper writes "increasing"; its proof shows $A'(Q)=QH'(Q)>0$, and $Q^*$, $r^*$ strictly monotone via (10) and Lemma 3, so the strict reading is taken. Existence and uniqueness of $Q^*$ are implicit in the paper's "Let $Q^*$ be the optimal order quantity" and in (10); they are stated here for every $K'>0$ so that part 4 is not vacuous. The paper's domain for $A$ is $[0,\infty)$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Lemma 6 and Eq. (10)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem area_lemma (M : QRModel) :
    StrictMonoOn (Afun M.G M.lam M.K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (Afun M.G M.lam M.K) ∧
    (∀ K' : ℝ, 0 < K' → ∃! Q : ℝ, IsOptQty M.G M.lam K' Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty M.G M.lam M.K Q ↔ Afun M.G M.lam M.K Q = M.lam * M.K)) ∧
    (∀ K₁ K₂ Q₁ Q₂ : ℝ, 0 < K₁ → K₁ < K₂ →
      IsOptQty M.G M.lam K₁ Q₁ → IsOptQty M.G M.lam K₂ Q₂ →
      Q₁ < Q₂ ∧ reorderPt M.G M.lam K₂ Q₂ < reorderPt M.G M.lam K₁ Q₁) := by sorry

end ZhengQR.CostBounds
