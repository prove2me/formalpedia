-- Prove2me | Theorems.Thm_levy_foundations_projectiveFamily_sigma_subadditive
-- name    : levy_foundations_projectiveFamily_sigma_subadditive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:16:42.898516+00:00
-- url     : https://prove2.me/theorems/578bfd06-f037-4128-8e21-3eb6e9d42868
-- title:
--   Sigma-subadditivity of the projective cylinder content
-- statement:
--   The finitely additive cylinder content induced by a projectively consistent family of finite-dimensional probability distributions on Polish Borel spaces is countably subadditive in the sense required by the extension construction.
-- source:
--   Shmuel Link, LeanLevy, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Processes/Kolmogorov.lean: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean (`sigma_subadditive`).

import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory

theorem levy_foundations_projectiveFamily_sigma_subadditive
  {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]
  (pf : LevyFoundations.ProjectiveFamily ι α) :
  (projectiveFamilyContent pf.consistent).IsSigmaSubadditive := by sorry
