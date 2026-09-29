-- Prove2me | Theorems.Thm_BanditAlgorithm_ftrl_regret_bound
-- name    : BanditAlgorithm.ftrl_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T17:01:52.815478+00:00
-- url     : https://prove2.me/theorems/a36337de-5610-46cd-977d-e6a3cba41a61
-- statement:
--   (Follow-the-regularised-leader regret bound, Theorem 28.5) Let $\eta > 0$, $F$ be convex with domain $D$ (differentiable at every iterate, an explicit hypothesis since the Lean Bregman divergence uses the total gradient), and $\mathcal{A}$ a non-empty convex set. If $a_1, a_2, \ldots$ are the (well-defined) FTRL iterates then for any comparator $a_0 \in \mathcal{A} \cap D$:
--
--   $$R_n(a_0) \le \frac{F(a_0)-F(a_1)}{\eta} + \sum_{t<n} \langle a_t - a_{t+1}, y_t\rangle - \frac{1}{\eta}\sum_{t<n} D_F(a_{t+1}, a_t).$$
-- source:
--   L&S Theorem 28.5, p.334

import Definitions.Def_OnlineLinearOptimization


open RealInnerProductSpace

theorem BanditAlgorithm.ftrl_regret_bound
    {d : ℕ} {η : ℝ} (hη : 0 < η)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {D 𝒜 : Set (EuclideanSpace ℝ (Fin d))}
    (hF : ConvexOn ℝ D F) (h𝒜conv : Convex ℝ 𝒜) (h𝒜ne : 𝒜.Nonempty)
    (y a : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hiter : IsFTRLIterates η F D 𝒜 y a)
    (hdiff : ∀ t, DifferentiableAt ℝ F (a t)) :
    ∀ a₀ ∈ 𝒜 ∩ D,
      oloRegret a y n a₀ ≤
        (F a₀ - F (a 0)) / η +
          ∑ t ∈ Finset.range n,
            (⟪a t - a (t + 1), y t⟫ - (1 / η) * bregmanDiv F (a (t + 1)) (a t)) := by
  sorry
