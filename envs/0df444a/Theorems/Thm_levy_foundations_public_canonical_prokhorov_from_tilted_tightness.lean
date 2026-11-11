-- Prove2me | Theorems.Thm_levy_foundations_public_canonical_prokhorov_from_tilted_tightness
-- name    : levy_foundations_public_canonical_prokhorov_from_tilted_tightness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:22:31.291204+00:00
-- url     : https://prove2.me/theorems/432dfef2-7c1a-40e1-8d8c-b50ffc2c2ded
-- title:
--   Canonical tilted-measure subsequence extraction from finite mass and tails
-- statement:
--   Given an eventually uniform total-mass bound for the semigroup's tilted scaled measures and uniformly small large-radius tails, construct a finite subsequential weak limit. The argument shifts to a small-time sequence, normalises each finite tilted measure with an atom at zero to a probability measure, applies tightness and Prokhorov, then rescales the limit and discards the added atom in tests with f(0)=0. This is the exact hard finite-measure compactness input to original ConvolutionSemigroup.exists_canonicalMeasure and to M5 Lévy measure extraction.
-- source:
--   Source-faithful decomposition of LeanLevy LevyKhintchineProof.lean theorem exists_canonicalMeasure (MIT-licensed, commit 7e73fd9b23ad52956ec2756a815889a783131ce4). Input total-mass lemma already Proved 32818; input tilted tail currently candidate pending. Root-connected original target 2a8d84b1-c82c-4941-987b-a4a8a1411f3f.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder
noncomputable section

theorem levy_foundations_public_canonical_prokhorov_from_tilted_tightness
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (C : ℝ≥0) (hC : 0 < C)
    (hmass : ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      S.tiltedScaledMeasure t Set.univ ≤ (C : ℝ≥0∞))
    (htail : ∀ (ε : ℝ), 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ (t : {t : ℝ // 0 < t}),
        S.tiltedScaledMeasure t (ProbabilityTheory.largeSet R) ≤ ENNReal.ofReal ε) :
    ∃ (η : Measure ℝ) (_ : IsFiniteMeasure η) (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
        Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
          atTop (𝓝 (∫ x, f x ∂η)) := by sorry
