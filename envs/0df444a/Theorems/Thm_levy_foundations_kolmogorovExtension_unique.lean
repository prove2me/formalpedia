-- Prove2me | Theorems.Thm_levy_foundations_kolmogorovExtension_unique
-- name    : levy_foundations_kolmogorovExtension_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:24:21.752342+00:00
-- url     : https://prove2.me/theorems/f652bddc-2c02-4046-a413-9b7b40608b6a
-- title:
--   Uniqueness of a projective-limit law from finite-dimensional marginals
-- statement:
--   Any two measures on the full product measurable space whose finite-dimensional marginals agree with the same projectively consistent Polish-space probability family coincide.
-- source:
--   Shmuel Link, LeanLevy, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Processes/Kolmogorov.lean: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean (`kolmogorovExtension_unique`, equivalent two-measure uniqueness statement).

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem levy_foundations_kolmogorovExtension_unique
  {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]
  (pf : LevyFoundations.ProjectiveFamily ι α)
  (μ ν : Measure (∀ i, α i))
  (hμ : IsProjectiveLimit μ pf.measure)
  (hν : IsProjectiveLimit ν pf.measure) :
  μ = ν := by sorry
