-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_tilted_mass_along_seq
-- name    : levy_foundations_public_semigroup_tilted_mass_along_seq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:29:24.301405+00:00
-- url     : https://prove2.me/theorems/9f810a8e-0854-45e0-959e-a20f6f1a53d2
-- title:
--   Eventual uniform mass of canonical tilted measures along vanishing times
-- statement:
--   For a vanishing positive sequence, the original canonical tilted scaled semigroup measures have an eventually uniform finite total-mass bound. This follows from the public small-jump second-moment bound and uniform large-jump mass bound.
-- source:
--   Source-exact tiltedScaledMeasure_mass_eventually_le calculation in LeanLevy/Levy/LevyKhintchineProof.lean, adapted to public Proved sequence-wise small-second-moment and all-time largeSet mass bounds. Required for canonical measure extraction d3cd6d70.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_tilted_mass_along_seq
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ n in atTop,
      S.tiltedScaledMeasure (t_seq n) Set.univ ≤ (C : ℝ≥0∞) := by
  sorry
