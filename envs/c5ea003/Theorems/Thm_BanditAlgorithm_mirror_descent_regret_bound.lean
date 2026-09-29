-- Prove2me | Theorems.Thm_BanditAlgorithm_mirror_descent_regret_bound
-- name    : BanditAlgorithm.mirror_descent_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T17:01:41.985844+00:00
-- url     : https://prove2.me/theorems/dcc47306-0ad8-4470-aa25-04318513ed01
-- statement:
--   (Mirror descent regret bound, Theorem 28.4) Let $\eta > 0$, $F$ be Legendre with domain $D$, and $\mathcal{A}$ a non-empty convex set with $\mathrm{int}(D) \cap \mathcal{A} \neq \emptyset$. If $a_1, a_2, \ldots$ are the (well-defined) mirror-descent iterates with unprojected dual iterates $\tilde a_{t+1}$, then for any comparator $a_0 \in \mathcal{A} \cap D$, both
--
--   $$R_n(a_0) \le \frac{F(a_0)-F(a_1)}{\eta} + \sum_{t<n} \langle a_t - a_{t+1}, y_t\rangle - \frac{1}{\eta}\sum_{t<n} D_F(a_{t+1}, a_t),$$
--
--   and (the Eq. (28.6)-conditioned second form, the condition being internalised in the iterate predicate as existence of the dual iterates)
--
--   $$R_n(a_0) \le \frac{1}{\eta}\Big(F(a_0) - F(a_1) + \sum_{t<n} D_F(a_t, \tilde a_{t+1})\Big).$$
-- source:
--   L&S Theorem 28.4, p.331

import Definitions.Def_OnlineLinearOptimization


open RealInnerProductSpace

theorem BanditAlgorithm.mirror_descent_regret_bound
    {d : ℕ} {η : ℝ} (hη : 0 < η)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {D 𝒜 : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsLegendre F D) (h𝒜conv : Convex ℝ 𝒜) (h𝒜ne : 𝒜.Nonempty)
    (hmeet : (interior D ∩ 𝒜).Nonempty)
    (y a ã : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hiter : IsMirrorDescentIterates η F D 𝒜 y a ã) :
    ∀ a₀ ∈ 𝒜 ∩ D,
      (oloRegret a y n a₀ ≤
        (F a₀ - F (a 0)) / η +
          ∑ t ∈ Finset.range n,
            (⟪a t - a (t + 1), y t⟫ - (1 / η) * bregmanDiv F (a (t + 1)) (a t))) ∧
      (oloRegret a y n a₀ ≤
        (1 / η) * (F a₀ - F (a 0) +
          ∑ t ∈ Finset.range n, bregmanDiv F (a t) (ã (t + 1)))) := by
  sorry
