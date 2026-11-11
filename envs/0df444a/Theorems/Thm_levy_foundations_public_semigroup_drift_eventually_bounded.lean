-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_drift_eventually_bounded
-- name    : levy_foundations_public_semigroup_drift_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:47:25.099375+00:00
-- url     : https://prove2.me/theorems/0fe64c60-e8fd-49af-b662-5e82d1c7dc5a
-- title:
--   Uniform boundedness of scaled truncated drift along vanishing semigroup times
-- statement:
--   The truncated first moment of a real convolution semigroup, divided by positive vanishing time, is eventually bounded. This is the substantive analytic estimate in LeanLevy ConvolutionSemigroup.drift_limit: bounded imaginary logarithmic derivative, small-ball second-moment control and large-jump mass control bound the drift uniformly. It is sufficient for the Bolzano–Weierstrass subsequence used by M5.
-- source:
--   Source-exact mathematical estimate (the hIm_bdd/hL/hS -> ha_bdd stage) from https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean, original lemma drift_limit. Public parent levy_foundations_public_semigroup_drift_subsequence, publication job 5055a895-828c-4953-84e8-59209d1554c0, and M5 joint extraction e8c8b930.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_drift_eventually_bounded
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      ((t_seq n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
        ∈ Set.Icc (-C) C := by sorry
