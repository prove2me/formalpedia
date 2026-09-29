-- Prove2me | Theorems.Thm_BanditAlgorithm_argmax_dist_le_of_unique_maximiser
-- name    : BanditAlgorithm.argmax_dist_le_of_unique_maximiser
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T04:19:17.558281+00:00
-- url     : https://prove2.me/theorems/fa555b3c-ddaf-4c87-b33f-e5e6881759d0
-- title:
--   Continuity of the $\arg\max$ at a unique maximiser
-- statement:
--   Let $S$ be a compact subset of a metric space, let $F:X\times A\to\mathbb R$ be continuous along $X\times S$, and suppose $a_0$ is the **only** maximiser of $F(x_0,\cdot)$ on $S$. Then for every $\varepsilon>0$ there is $\delta>0$ such that every maximiser of $F(x,\cdot)$ lies within $\varepsilon$ of $a_0$ whenever $d(x,x_0)<\delta$.
--
--   This is the argmax half of Berge's maximum theorem, specialised to a singleton argmax, where the set-valued upper hemicontinuity becomes an ordinary continuity statement. Nothing is assumed about maximisers at nearby parameters: they may well fail to be unique, and the conclusion still constrains all of them.
--
--   The proof is compactness and contradiction. If the conclusion fails there are $x_n\to x_0$ and maximisers $a_n$ of $F(x_n,\cdot)$ with $d(a_n,a_0)\ge\varepsilon$; compactness extracts a convergent subsequence $a_{\varphi(n)}\to a$, still $\varepsilon$ away from $a_0$; and passing to the limit in $F(x_{\varphi(n)},a_{\varphi(n)})\ge F(x_{\varphi(n)},b)$ for fixed $b\in S$ shows $a$ maximises $F(x_0,\cdot)$, contradicting uniqueness.
--
--   Continuity is required only along the feasible set $X\times S$, which matters in applications where the objective is genuinely discontinuous off it. Uniqueness cannot be dropped: a selection of maximisers can jump between two of them arbitrarily.
-- source:
--   Argmax (upper hemicontinuity) half of Berge's maximum theorem at a point of unique maximisation; C. Berge, Espaces topologiques, fonctions multivoques (1959), Ch. VI.

import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact

open Filter Topology Metric

theorem BanditAlgorithm.argmax_dist_le_of_unique_maximiser {X A : Type*}
    [MetricSpace X] [MetricSpace A] {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun q : X × A ↦ F q.1 q.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A}
    (huniq : ∀ a, a ∈ S → (∀ b ∈ S, F x₀ b ≤ F x₀ a) → a = a₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : X, dist x x₀ < δ →
      ∀ a : A, a ∈ S → (∀ b ∈ S, F x b ≤ F x a) → dist a a₀ < ε := by
  sorry
