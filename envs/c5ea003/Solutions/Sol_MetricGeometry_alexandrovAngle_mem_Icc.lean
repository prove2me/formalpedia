-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T22:53:07.203355+00:00
-- url     : https://prove2.me/submissions/55735319-903c-4722-bb85-2df69797427e

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (p : X) (g1 g2 : ℝ → X) :
    alexandrovAngle p g1 g2 ∈ Set.Icc 0 Real.pi := by
  set F : Filter (ℝ × ℝ) := (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)) with hF
  set u : ℝ × ℝ → ℝ := fun st => comparisonAngle p (g1 st.1) (g2 st.2) with hu
  have hb : ∀ st : ℝ × ℝ, u st ∈ Set.Icc 0 Real.pi := fun st =>
    MetricGeometry.comparisonAngle_mem_Icc p (g1 st.1) (g2 st.2)
  have hne : F.NeBot := by rw [hF]; infer_instance
  have hbdd : F.IsBoundedUnder (· ≤ ·) u := isBoundedUnder_of ⟨Real.pi, fun st => (hb st).2⟩
  have key : ∀ b : ℝ, (∀ᶠ st in F, u st ≤ b) → 0 ≤ b := by
    intro b hbb
    obtain ⟨st, hst⟩ := hbb.exists
    exact le_trans (hb st).1 hst
  constructor
  · exact le_limsup_of_le hbdd key
  · refine limsup_le_of_le ?_ (Eventually.of_forall fun st => (hb st).2)
    exact ⟨0, fun a ha => key a (by simpa using ha)⟩
