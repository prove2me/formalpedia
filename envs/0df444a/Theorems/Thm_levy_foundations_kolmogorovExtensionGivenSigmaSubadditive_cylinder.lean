-- Prove2me | Theorems.Thm_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder
-- name    : levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:29:42.076834+00:00
-- url     : https://prove2.me/theorems/60e31875-4937-4a45-9036-fd3a9f37e141
-- title:
--   Kolmogorov extension evaluates measurable cylinder sets
-- statement:
--   Kolmogorov extension evaluates measurable cylinder sets.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean#L371

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Definitions.Def_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive
open MeasureTheory

theorem levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_cylinder
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (hσ : (projectiveFamilyContent pf.consistent).IsSigmaSubadditive)
    (I : Finset ι) {S : Set (∀ i : I, α i)} (hS : MeasurableSet S) :
    LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive pf hσ (cylinder I S) =
      pf.measure I S := by sorry
