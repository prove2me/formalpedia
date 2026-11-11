-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound
-- name    : levy_foundations_public_semigroup_scaled_largeSet_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:51:28.242323+00:00
-- url     : https://prove2.me/theorems/ba89e103-e067-4ec7-8ada-89d6391b6da1
-- title:
--   Uniform scaled mass bound outside any fixed positive radius
-- statement:
--   For each fixed ε>0, the mass of {|x|≥ε} under the semigroup measure μ_t grows at most linearly in t, uniformly over all t>0. The proof uses a nonnegative frequency-integrated cosine deficit, Fubini, the semigroup exponent bound and a compact maximum of |ψ|. This is the public source-exact version of the original private LeanLevy scaled_mass_bound_real and is required for the M5 drift bound and Lévy-measure extraction.
-- source:
--   Original LeanLevy LevyKhintchineProof.lean, ConvolutionSemigroup.scaled_mass_bound_real; https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Four explicit public sublemmas are independently proved/awaiting proof verdict. M5 parent drift eventual boundedness 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
import Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
import Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_largeSet_mass_bound
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (ProbabilityTheory.largeSet ε)).toReal ≤ ↑C := by sorry
