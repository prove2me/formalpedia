-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_nonglobal_edge_direction
-- name    : BanditAlgorithm.partial_monitoring_nonglobal_edge_direction
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:24:59.513906+00:00
-- url     : https://prove2.me/theorems/4606da5f-651f-4ce4-b1a7-4f8a44e398ea
-- title:
--   A non-globally-observable edge has a feedback-invisible loss direction
-- statement:
--   Fix two actions $a,b$ in a finite partial-monitoring game. If their loss difference cannot be reconstructed from the feedback of all actions, then there is an outcome-space direction $q$ with zero total mass such that
--
--   $$
--   \langle L_a-L_b,q\rangle=1,\qquad\sum_{i:\,\Phi_{c i}=\sigma}q_i=0\quad\text{for every action $c$ and signal $\sigma$}.
--   $$
--
--   Thus perturbing an outcome distribution in the directions $\pm q$ changes the relative loss of $a$ and $b$ while leaving every action's signal law unchanged. This is the linear-algebraic separation step behind the hopeless-game lower bound.
--
--   **Formalization Note** The normalization to inner product one is possible because non-observability says the loss-difference vector has a nonzero component orthogonal to the stacked feedback range.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.13 proof, printed pp. 491–492 (PDF pp. 499–500), together with the orthogonal-separation construction used in Theorem 37.12, Step 1, Eq. (37.6), printed pp. 489–490; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_nonglobal_edge_direction
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hn_global : ¬ ∃ f : Fin k × 𝕊 → ℝ, IsGlobalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 := by
  sorry
