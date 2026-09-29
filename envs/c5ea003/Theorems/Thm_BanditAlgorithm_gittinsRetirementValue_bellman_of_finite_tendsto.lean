-- Prove2me | Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_bellman_of_finite_tendsto
-- name    : BanditAlgorithm.gittinsRetirementValue_bellman_of_finite_tendsto
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:51:15.436944+00:00
-- url     : https://prove2.me/theorems/89b47fa8-2e97-428f-8e39-caa8faaa889d
-- title:
--   The finite Bellman recursion passes to the infinite-horizon retirement value
-- statement:
--   Let $V_n^{\gamma}$ be the finite-horizon Bellman values of the discounted one-armed retirement game, and let $v_{\gamma}$ be its infinite-horizon value. Assume that $V_n^{\gamma}(x)$ converges pointwise to $v_{\gamma}(x)$ and that both the finite values and the limit have the stated integrability against every transition measure.
--
--   For every state $x$, the infinite-horizon value then satisfies the Wald--Bellman equation
--
--   $$
--   v_{\gamma}(x)=\max\left\{0,\;r(x)-\gamma+\alpha\int v_{\gamma}(y)\,P(x,dy)\right\}.
--   $$
--
--   This result isolates the analytic passage from finite-horizon dynamic programming to the infinite-horizon Bellman fixed point used in the proof of the Gittins index theorem.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), printed pp. 442-443, Theorem 35.3 (Wald--Bellman equation), specialized to the discounted retirement value used in printed p. 449, Lemma 35.7(a).

import Definitions.Def_GittinsFiniteRetirementValue
import Mathlib.Topology.Instances.Real.Lemmas

open MeasureTheory ProbabilityTheory Filter Topology

theorem BanditAlgorithm.gittinsRetirementValue_bellman_of_finite_tendsto
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} {α γ : ℝ} (hα0 : 0 ≤ α)
    (hfin : ∀ n x,
      Integrable (gittinsFiniteRetirementValue P r α γ n) (P x))
    (hlim : ∀ x, Integrable (gittinsRetirementValue P r α γ) (P x))
    (hconv : ∀ x,
      Tendsto (fun n ↦ gittinsFiniteRetirementValue P r α γ n x)
        atTop (𝓝 (gittinsRetirementValue P r α γ x)))
    (x : S) :
    gittinsRetirementValue P r α γ x =
      max 0 (r x - γ +
        α * ∫ y, gittinsRetirementValue P r α γ y ∂P x) := by
  sorry
