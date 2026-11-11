-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_drift_subsequence
-- name    : levy_foundations_public_semigroup_drift_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:37:11.498981+00:00
-- url     : https://prove2.me/theorems/b1dd0575-a358-4695-95cd-ae87e6b04676
-- title:
--   M5 public drift subsequence selection along a vanishing time sequence
-- statement:
--   Under any positive truncation radius at most one, scaled first moments of a real convolution semigroup admit a convergent subsequence along each positive time sequence tending to zero. Exact public interface of LeanLevy ConvolutionSemigroup.drift_limit, allowing the M5 joint extraction to select drift without importing a private theorem.
-- source:
--   Source-faithful public interface of LeanLevy LevyKhintchineProof.lean lemma ConvolutionSemigroup.drift_limit; https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Parent levy_foundations_public_semigroup_joint_smalltime_triplet_data e8c8b930-909f-4093-973b-161264070bab; original theorem 9c72a88a private Open.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_drift_subsequence
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ b : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n =>
        (t_seq (φ n)).val⁻¹ *
          ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq (φ n)) : Measure ℝ))
        atTop (𝓝 b) := by sorry
