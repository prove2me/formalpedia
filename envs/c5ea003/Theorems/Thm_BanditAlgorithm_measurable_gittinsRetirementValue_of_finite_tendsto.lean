-- Prove2me | Theorems.Thm_BanditAlgorithm_measurable_gittinsRetirementValue_of_finite_tendsto
-- name    : BanditAlgorithm.measurable_gittinsRetirementValue_of_finite_tendsto
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T05:09:01.145627+00:00
-- url     : https://prove2.me/theorems/6d623114-0044-457f-9e37-a8f25338b6e3
-- title:
--   Measurability of the infinite-horizon retirement value from finite Bellman convergence
-- statement:
--   Let $V_n^{\gamma}$ be the measurable finite-horizon Bellman values of a discounted one-armed retirement game, and suppose that they converge pointwise to the infinite-horizon retirement value $v_{\gamma}$:
--
--   $$
--   V_n^{\gamma}(x)\longrightarrow v_{\gamma}(x)
--   \qquad\text{for every state }x.
--   $$
--
--   Then the map $x\mapsto v_{\gamma}(x)$ is measurable.
--
--   This is the measurability step needed to define threshold stopping rules from sublevel sets of the retirement value and, through the fair-charge characterization, of the Gittins index.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), printed pp. 442-443, Theorem 35.3 and the following note that measurability is the technical issue; specialized to printed p. 449, Lemma 35.7.

import Definitions.Def_GittinsFiniteRetirementValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory ProbabilityTheory Filter Topology

theorem BanditAlgorithm.measurable_gittinsRetirementValue_of_finite_tendsto
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ)
    (hconv : ∀ x,
      Tendsto (fun n ↦ gittinsFiniteRetirementValue P r α γ n x)
        atTop (𝓝 (gittinsRetirementValue P r α γ x))) :
    Measurable (gittinsRetirementValue P r α γ) := by
  sorry
