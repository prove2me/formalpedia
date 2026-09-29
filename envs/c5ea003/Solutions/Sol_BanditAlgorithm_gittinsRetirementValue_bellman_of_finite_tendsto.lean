-- Prove2me | solution 1 for BanditAlgorithm.gittinsRetirementValue_bellman_of_finite_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:51:16.137607+00:00
-- url     : https://prove2.me/submissions/e6d036b3-ce04-4da4-94ea-63c66c40bda2

import Theorems.Thm_BanditAlgorithm_gittinsFiniteRetirementValue_mono_of_integrable
import Mathlib.Topology.Instances.Real.Lemmas

open MeasureTheory ProbabilityTheory Filter Topology
open BanditAlgorithm

theorem solution
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
  have hmono := gittinsFiniteRetirementValue_mono_of_integrable
    P r α γ hα0 hfin
  have hint_tendsto :
      Tendsto
        (fun n ↦ ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x)
        atTop
        (𝓝 (∫ y, gittinsRetirementValue P r α γ y ∂P x)) := by
    apply integral_tendsto_of_tendsto_of_monotone
    · exact fun n ↦ hfin n x
    · exact hlim x
    · exact Filter.Eventually.of_forall fun y ↦
        monotone_nat_of_le_succ fun n ↦ hmono n y
    · exact Filter.Eventually.of_forall hconv
  have hright :
      Tendsto
        (fun n ↦ max 0 (r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x))
        atTop
        (𝓝 (max 0 (r x - γ +
          α * ∫ y, gittinsRetirementValue P r α γ y ∂P x))) :=
    tendsto_const_nhds.max
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hint_tendsto))
  have hleft :
      Tendsto
        (fun n ↦ gittinsFiniteRetirementValue P r α γ (n + 1) x)
        atTop
        (𝓝 (gittinsRetirementValue P r α γ x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hconv x)
  have hfun :
      (fun n ↦ gittinsFiniteRetirementValue P r α γ (n + 1) x) =
        (fun n ↦ max 0 (r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x)) := by
    funext n
    rfl
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright
