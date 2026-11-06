-- Prove2me | Theorems.Thm_levy_foundations_kolmogorovExtension_exists
-- name    : levy_foundations_kolmogorovExtension_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:23:08.860987+00:00
-- url     : https://prove2.me/theorems/fc6e2fc0-6d29-4871-bb00-014318df368a
-- title:
--   Kolmogorov extension theorem for consistent Polish-space marginals
-- statement:
--   Every projectively consistent collection of finite-dimensional probability distributions on Borel Polish coordinate spaces extends to a measure on the full product space with exactly those finite-dimensional marginals. No limiting measure or σ-additivity certificate is assumed.
-- source:
--   Shmuel Link, LeanLevy, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Processes/Kolmogorov.lean: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean (`kolmogorovExtension`, `isProjectiveLimit_kolmogorovExtension`).

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem levy_foundations_kolmogorovExtension_exists
  {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]
  (pf : LevyFoundations.ProjectiveFamily ι α) :
  ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ pf.measure := by sorry
