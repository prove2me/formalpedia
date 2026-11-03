-- Prove2me | Theorems.Thm_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_limit
-- name    : levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:28:33.17213+00:00
-- url     : https://prove2.me/theorems/ea962684-957a-4a35-a410-0dc9078a3165
-- title:
--   Canonical Kolmogorov extension has the required finite marginals
-- statement:
--   Canonical Kolmogorov extension has the required finite marginals.
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

theorem levy_foundations_kolmogorovExtensionGivenSigmaSubadditive_limit
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (hσ : (projectiveFamilyContent pf.consistent).IsSigmaSubadditive) :
    IsProjectiveLimit (LevyFoundations.kolmogorovExtensionGivenSigmaSubadditive pf hσ) pf.measure := by sorry
