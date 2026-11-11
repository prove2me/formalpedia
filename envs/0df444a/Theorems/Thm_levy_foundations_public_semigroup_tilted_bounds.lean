-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_tilted_bounds
-- name    : levy_foundations_public_semigroup_tilted_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:39:02.73493+00:00
-- url     : https://prove2.me/theorems/cb2d54b9-d967-45cb-afda-e19d86d32e22
-- title:
--   M5 small-time sequence with bounded tilted mass and tight scaled tails
-- statement:
--   Select one positive time sequence tending to zero for which the full min(1,x²)-weighted scaled semigroup mass is uniformly bounded and the scaled mass outside large spatial radii is uniformly small. The bound is assembled from the proved eventual small-ball second-moment estimate, the proved large-set mass estimate, and the new uniform large-tail theorem; drop a finite initial prefix of the standard sequence to turn eventual bounds into all-index bounds.
-- source:
--   Mathematically necessary source-exact semigroup estimate for weighted Prokhorov extraction. Parent a407ec20-f0b2-46a7-a269-5aaad3eb2279 consumes this with general weighted Prokhorov theorem in the new accepted reduction route; no circular dependence on M5 root.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_tilted_bounds
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)) ∧
      (∃ C : ℝ, ∀ n,
        (t_seq n).val⁻¹ *
          ∫ x, min (1 : ℝ) (x ^ 2) ∂(S.measure (t_seq n) : Measure ℝ) ≤ C) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
        ∀ n,
          (t_seq n).val⁻¹ *
            ((S.measure (t_seq n) : Measure ℝ) (largeSet R)).toReal ≤ δ) := by sorry
