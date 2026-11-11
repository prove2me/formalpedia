-- Prove2me | Theorems.Thm_levy_foundations_public_tilted_cofinal_mass_sequence
-- name    : levy_foundations_public_tilted_cofinal_mass_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:24:51.537433+00:00
-- url     : https://prove2.me/theorems/3ba92292-02bf-40ff-a2ac-658c9563da3c
-- title:
--   Select a cofinal small-time sequence satisfying an eventual tilted mass bound at every index
-- statement:
--   From a bound on the total mass of tilted scaled semigroup measures that holds eventually as time approaches zero, construct a concrete positive sequence t_n tending to zero along which the bound holds at every index. Use t_n=1/(n+2) shifted past the eventuality threshold. This is the first independently provable 25-line step of the original canonical Prokhorov extraction.
-- source:
--   Extracted from LeanLevy source theorem ConvolutionSemigroup.exists_canonicalMeasure original steps 1-2. Parent conditional Prokhorov child 432dfef2-7c1a-40e1-8d8c-b50ffc2c2ded; M5 canonical target 2a8d84b1-c82c-4941-987b-a4a8a1411f3f.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_tilted_cofinal_mass_sequence
    (S : ProbabilityTheory.ConvolutionSemigroup) (C : ℝ≥0)
    (hmass : ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      S.tiltedScaledMeasure t Set.univ ≤ (C : ℝ≥0∞)) :
    ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ n, S.tiltedScaledMeasure (t_seq n) Set.univ ≤ (C : ℝ≥0∞) := by sorry
